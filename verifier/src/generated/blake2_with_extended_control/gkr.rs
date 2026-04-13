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
    const DESCS: [(usize, usize, usize); 547usize] = [
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
        (1usize, 40usize, 0usize),
        (1usize, 41usize, 0usize),
        (1usize, 42usize, 0usize),
        (1usize, 43usize, 0usize),
        (1usize, 44usize, 0usize),
        (2usize, 45usize, 46usize),
        (2usize, 47usize, 48usize),
        (2usize, 49usize, 50usize),
        (2usize, 51usize, 52usize),
        (2usize, 53usize, 54usize),
        (2usize, 55usize, 56usize),
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
        (2usize, 97usize, 98usize),
        (2usize, 99usize, 100usize),
        (2usize, 101usize, 102usize),
        (2usize, 103usize, 104usize),
        (2usize, 105usize, 106usize),
        (2usize, 107usize, 108usize),
        (2usize, 109usize, 110usize),
        (2usize, 111usize, 112usize),
        (2usize, 113usize, 114usize),
        (2usize, 115usize, 116usize),
        (2usize, 117usize, 118usize),
        (2usize, 119usize, 120usize),
        (2usize, 121usize, 122usize),
        (2usize, 123usize, 124usize),
        (2usize, 125usize, 126usize),
        (2usize, 127usize, 128usize),
        (2usize, 129usize, 130usize),
        (2usize, 131usize, 132usize),
        (1usize, 133usize, 0usize),
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
        (2usize, 160usize, 161usize),
        (2usize, 162usize, 163usize),
        (2usize, 164usize, 165usize),
        (2usize, 166usize, 167usize),
        (2usize, 168usize, 169usize),
        (2usize, 170usize, 171usize),
        (2usize, 172usize, 173usize),
        (2usize, 174usize, 175usize),
        (2usize, 176usize, 177usize),
        (2usize, 178usize, 179usize),
        (2usize, 180usize, 181usize),
        (2usize, 182usize, 183usize),
        (2usize, 184usize, 185usize),
        (2usize, 186usize, 187usize),
        (2usize, 188usize, 189usize),
        (2usize, 190usize, 191usize),
        (2usize, 192usize, 193usize),
        (2usize, 194usize, 195usize),
        (2usize, 196usize, 197usize),
        (2usize, 198usize, 199usize),
        (2usize, 200usize, 201usize),
        (2usize, 202usize, 203usize),
        (2usize, 204usize, 205usize),
        (2usize, 206usize, 207usize),
        (2usize, 208usize, 209usize),
        (2usize, 210usize, 211usize),
        (2usize, 212usize, 213usize),
        (2usize, 214usize, 215usize),
        (2usize, 216usize, 217usize),
        (2usize, 218usize, 219usize),
        (2usize, 220usize, 221usize),
        (2usize, 222usize, 223usize),
        (2usize, 224usize, 225usize),
        (2usize, 226usize, 227usize),
        (2usize, 228usize, 229usize),
        (2usize, 230usize, 231usize),
        (2usize, 232usize, 233usize),
        (2usize, 234usize, 235usize),
        (2usize, 236usize, 237usize),
        (2usize, 238usize, 239usize),
        (2usize, 240usize, 241usize),
        (2usize, 242usize, 243usize),
        (2usize, 244usize, 245usize),
        (2usize, 246usize, 247usize),
        (2usize, 248usize, 249usize),
        (2usize, 250usize, 251usize),
        (2usize, 252usize, 253usize),
        (2usize, 254usize, 255usize),
        (2usize, 256usize, 257usize),
        (2usize, 258usize, 259usize),
        (2usize, 260usize, 261usize),
        (2usize, 262usize, 263usize),
        (2usize, 264usize, 265usize),
        (2usize, 266usize, 267usize),
        (2usize, 268usize, 269usize),
        (2usize, 270usize, 271usize),
        (2usize, 272usize, 273usize),
        (2usize, 274usize, 275usize),
        (2usize, 276usize, 277usize),
        (2usize, 278usize, 279usize),
        (2usize, 280usize, 281usize),
        (2usize, 282usize, 283usize),
        (2usize, 284usize, 285usize),
        (2usize, 286usize, 287usize),
        (2usize, 288usize, 289usize),
        (2usize, 290usize, 291usize),
        (2usize, 292usize, 293usize),
        (2usize, 294usize, 295usize),
        (2usize, 296usize, 297usize),
        (2usize, 298usize, 299usize),
        (2usize, 300usize, 301usize),
        (2usize, 302usize, 303usize),
        (2usize, 304usize, 305usize),
        (2usize, 306usize, 307usize),
        (2usize, 308usize, 309usize),
        (2usize, 310usize, 311usize),
        (2usize, 312usize, 313usize),
        (2usize, 314usize, 315usize),
        (2usize, 316usize, 317usize),
        (2usize, 318usize, 319usize),
        (2usize, 320usize, 321usize),
        (2usize, 322usize, 323usize),
        (2usize, 324usize, 325usize),
        (2usize, 326usize, 327usize),
        (2usize, 328usize, 329usize),
        (2usize, 330usize, 331usize),
        (2usize, 332usize, 333usize),
        (2usize, 334usize, 335usize),
        (2usize, 336usize, 337usize),
        (2usize, 338usize, 339usize),
        (2usize, 340usize, 341usize),
        (1usize, 342usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
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
    while i < 547usize {
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
            [(1usize, [868usize, 0usize, 0usize, 0usize])];
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
                [3usize, 2usize, 646usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 647usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 648usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 649usize, 0usize, 0usize, 0usize],
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
                [3usize, 0usize, 648usize, 0usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 650usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 651usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 652usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 653usize, 0usize, 0usize, 0usize],
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
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 648usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 649usize, 0usize, 0usize, 0usize],
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
                [3usize, 0usize, 648usize, 0usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 654usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 655usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1073741816usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 656usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 657usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 658usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 659usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 134217711usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 662usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 663usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 664usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 665usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1073741816usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 660usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 661usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 134217711usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 666usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 667usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1207959527usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 668usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 669usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 670usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 671usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 268435422usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 674usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 675usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 676usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 677usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1207959527usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 672usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 673usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 268435422usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 678usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 679usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1342177238usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 680usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 681usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 682usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 683usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 402653133usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 686usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 687usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 688usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 689usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1342177238usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 684usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 685usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 402653133usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 690usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 691usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1476394949usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 692usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 693usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 694usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 695usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 536870844usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 698usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 699usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 700usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 701usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1476394949usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 696usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 697usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 536870844usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 702usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 703usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1610612660usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 704usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 705usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 706usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 707usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 671088555usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 710usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 711usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 712usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 713usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1610612660usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 708usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 709usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 671088555usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 714usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 715usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1744830371usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 716usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 717usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 718usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 719usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 805306266usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 722usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 723usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 724usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 725usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1744830371usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 720usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 721usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 805306266usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 726usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 727usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1879048082usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 728usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 729usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 730usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 731usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 939523977usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 734usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 735usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 736usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 737usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1879048082usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 732usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 733usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 939523977usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 738usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 739usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 2013265793usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 740usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 741usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 742usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 743usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1073741688usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 746usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 747usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 748usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 749usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 2013265793usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 744usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 745usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1073741688usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 750usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 751usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 134217583usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 752usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 753usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 754usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 755usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1207959399usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 758usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 759usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 760usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 761usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 134217583usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 756usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 757usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1207959399usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 762usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 763usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 268435294usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 764usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 765usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 766usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 767usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1342177110usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 770usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 771usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 772usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 773usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 268435294usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 768usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 769usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1342177110usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 774usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 775usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 402653005usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 776usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 777usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 778usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 779usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1476394821usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 782usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 783usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 784usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 785usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 402653005usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 780usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 781usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 1476394821usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 786usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 787usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 536870716usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 788usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 789usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 790usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 791usize, 0usize, 0usize, 0usize],
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
                [3usize, 2usize, 794usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 795usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 796usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 797usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 648usize, 536870716usize, 0usize, 0usize],
                [3usize, 1usize, 649usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 792usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 793usize, 0usize, 0usize, 0usize],
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
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 796usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 797usize, 0usize, 0usize, 0usize],
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
                [3usize, 0usize, 796usize, 0usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 798usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 799usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 800usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 801usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 1073741816usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 802usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 803usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 804usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 805usize, 0usize, 0usize, 0usize],
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
                [3usize, 0usize, 796usize, 0usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 800usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 801usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 1073741816usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 804usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 805usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 134217711usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 806usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 807usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 808usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 809usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 1207959527usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 810usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 811usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 812usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 813usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 134217711usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 808usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 809usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 1207959527usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 812usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 813usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 268435422usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 814usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 815usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 816usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 817usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 1342177238usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 818usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 819usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 820usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 821usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 268435422usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 816usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 817usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 1342177238usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 820usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 821usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 402653133usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 822usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 823usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 824usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 825usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 1476394949usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 826usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 827usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 828usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 829usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 402653133usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 824usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 825usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 1476394949usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 828usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 829usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 536870844usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 830usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 831usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 832usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 833usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 1610612660usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 834usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 835usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 836usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 837usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 536870844usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 832usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 833usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 1610612660usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 836usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 837usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 671088555usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 838usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 839usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 840usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 841usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 1744830371usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 842usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 843usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 844usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 845usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 671088555usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 840usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 841usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 1744830371usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 844usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 845usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 805306266usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 846usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 847usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 848usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 849usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 1879048082usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 850usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 851usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 852usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 853usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 805306266usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 848usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 849usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 1879048082usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 852usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 853usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 939523977usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 854usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 855usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 856usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 857usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 2013265793usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 858usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 859usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 860usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 861usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 939523977usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 856usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 857usize, 0usize, 0usize, 0usize],
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
                [5usize, 0usize, 796usize, 2013265793usize, 0usize, 0usize],
                [3usize, 1usize, 797usize, 0usize, 0usize, 0usize],
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 860usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 861usize, 0usize, 0usize, 0usize],
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
                [3usize, 2usize, 862usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 863usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 864usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 865usize, 0usize, 0usize, 0usize],
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
                [4usize, 0usize, 939519849usize, 0usize, 0usize, 0usize],
                [3usize, 2usize, 869usize, 0usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
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
                [5usize, 2usize, 869usize, 536870908usize, 0usize, 0usize],
                [3usize, 3usize, 870usize, 0usize, 0usize, 0usize],
                [3usize, 4usize, 866usize, 0usize, 0usize, 0usize],
                [3usize, 5usize, 867usize, 0usize, 0usize, 0usize],
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
                [4usize, 0usize, 939519849usize, 0usize, 0usize, 0usize],
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
        const SIMPLE_GATES: [(usize, [usize; 4]); 1usize] =
            [(6usize, [869usize, 644usize, 875usize, 0usize])];
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
            const A_VAL_TERMS: [(usize, usize); 1usize] = [(870usize, 268435454usize)];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 0usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (646usize, 268435454usize),
                (601usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (647usize, 268435454usize),
                (601usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (650usize, 268435454usize),
                (602usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (651usize, 268435454usize),
                (602usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (656usize, 268435454usize),
                (603usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (657usize, 268435454usize),
                (603usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (662usize, 268435454usize),
                (604usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (663usize, 268435454usize),
                (604usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (668usize, 268435454usize),
                (605usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (669usize, 268435454usize),
                (605usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (674usize, 268435454usize),
                (606usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (675usize, 268435454usize),
                (606usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (680usize, 268435454usize),
                (607usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (681usize, 268435454usize),
                (607usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (686usize, 268435454usize),
                (608usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (687usize, 268435454usize),
                (608usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (692usize, 268435454usize),
                (609usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (693usize, 268435454usize),
                (609usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (698usize, 268435454usize),
                (610usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (699usize, 268435454usize),
                (610usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (704usize, 268435454usize),
                (611usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (705usize, 268435454usize),
                (611usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (710usize, 268435454usize),
                (612usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (711usize, 268435454usize),
                (612usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (716usize, 268435454usize),
                (613usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (717usize, 268435454usize),
                (613usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (722usize, 268435454usize),
                (614usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (723usize, 268435454usize),
                (614usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (728usize, 268435454usize),
                (615usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (729usize, 268435454usize),
                (615usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (734usize, 268435454usize),
                (616usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (735usize, 268435454usize),
                (616usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (740usize, 268435454usize),
                (617usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (741usize, 268435454usize),
                (617usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (746usize, 268435454usize),
                (618usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (747usize, 268435454usize),
                (618usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (752usize, 268435454usize),
                (619usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (753usize, 268435454usize),
                (619usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (758usize, 268435454usize),
                (620usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (759usize, 268435454usize),
                (620usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (764usize, 268435454usize),
                (621usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (765usize, 268435454usize),
                (621usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (770usize, 268435454usize),
                (622usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (771usize, 268435454usize),
                (622usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (776usize, 268435454usize),
                (623usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (777usize, 268435454usize),
                (623usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (782usize, 268435454usize),
                (624usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (783usize, 268435454usize),
                (624usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (788usize, 268435454usize),
                (625usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (789usize, 268435454usize),
                (625usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (794usize, 268435454usize),
                (626usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (795usize, 268435454usize),
                (626usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (798usize, 268435454usize),
                (627usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (799usize, 268435454usize),
                (627usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (802usize, 268435454usize),
                (628usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (803usize, 268435454usize),
                (628usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (806usize, 268435454usize),
                (629usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (807usize, 268435454usize),
                (629usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (810usize, 268435454usize),
                (630usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (811usize, 268435454usize),
                (630usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (814usize, 268435454usize),
                (631usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (815usize, 268435454usize),
                (631usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (818usize, 268435454usize),
                (632usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (819usize, 268435454usize),
                (632usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (822usize, 268435454usize),
                (633usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (823usize, 268435454usize),
                (633usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (826usize, 268435454usize),
                (634usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (827usize, 268435454usize),
                (634usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (830usize, 268435454usize),
                (635usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (831usize, 268435454usize),
                (635usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (834usize, 268435454usize),
                (636usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (835usize, 268435454usize),
                (636usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (838usize, 268435454usize),
                (637usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (839usize, 268435454usize),
                (637usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (842usize, 268435454usize),
                (638usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (843usize, 268435454usize),
                (638usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (846usize, 268435454usize),
                (639usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (847usize, 268435454usize),
                (639usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (850usize, 268435454usize),
                (640usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (851usize, 268435454usize),
                (640usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (854usize, 268435454usize),
                (641usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (855usize, 268435454usize),
                (641usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (858usize, 268435454usize),
                (642usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (859usize, 268435454usize),
                (642usize, 1744830467usize),
            ];
            let mut a_val = eval_linear_relation(evals, &A_VAL_TERMS, 133099247usize, j);
            const B_VAL_TERMS: [(usize, usize); 3usize] = [
                (869usize, 1744830467usize),
                (862usize, 268435454usize),
                (643usize, 133099247usize),
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
                (870usize, 1744830467usize),
                (863usize, 268435454usize),
                (643usize, 1744830467usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (136usize, 268435454usize),
                (133usize, 268435454usize),
                (135usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            field_ops::add_assign(&mut a_val, &lookup_additive_challenge);
            let c_val = evals.get_unchecked(645usize)[j];
            const D_VAL_COLS: [(usize, usize); 4usize] = [
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const D_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (874usize, 268435454usize),
                (873usize, 268435454usize),
                (872usize, 268435454usize),
                (871usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 6usize),
                (0usize, 2usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 9usize] = [
                (137usize, 268435454usize),
                (16usize, 16777216usize),
                (32usize, 16777216usize),
                (97usize, 16777216usize),
                (129usize, 1744831011usize),
                (130usize, 1476396101usize),
                (133usize, 1996488705usize),
                (59usize, 16777216usize),
                (135usize, 1996488705usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (139usize, 268435454usize),
                (134usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 8usize),
                (0usize, 2usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 11usize] = [
                (140usize, 268435454usize),
                (18usize, 16777216usize),
                (34usize, 16777216usize),
                (98usize, 16777216usize),
                (129usize, 16777216usize),
                (130usize, 33554432usize),
                (131usize, 1744831011usize),
                (132usize, 1476396101usize),
                (134usize, 1996488705usize),
                (60usize, 16777216usize),
                (138usize, 1996488705usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (536870876usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (149usize, 268435454usize),
                (143usize, 268435454usize),
                (147usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (150usize, 268435454usize),
                (144usize, 268435454usize),
                (148usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (805306330usize, 0usize),
                (0usize, 1usize),
                (0usize, 6usize),
                (0usize, 3usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (151usize, 268435454usize),
                (47usize, 1048576usize),
                (139usize, 1048576usize),
                (140usize, 268435456usize),
                (141usize, 1744830499usize),
                (143usize, 2012217345usize),
                (144usize, 2004877313usize),
                (32usize, 1048576usize),
                (147usize, 2012217345usize),
                (148usize, 2004877313usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (536870876usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (154usize, 268435454usize),
                (145usize, 268435454usize),
                (152usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (155usize, 268435454usize),
                (146usize, 268435454usize),
                (153usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (805306330usize, 0usize),
                (0usize, 1usize),
                (0usize, 7usize),
                (0usize, 3usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 11usize] = [
                (156usize, 268435454usize),
                (48usize, 1048576usize),
                (136usize, 1048576usize),
                (137usize, 268435456usize),
                (141usize, 1048576usize),
                (142usize, 1744830499usize),
                (145usize, 2012217345usize),
                (146usize, 2004877313usize),
                (34usize, 1048576usize),
                (152usize, 2012217345usize),
                (153usize, 2004877313usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (163usize, 268435454usize),
                (161usize, 268435454usize),
                (139usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 12usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 14usize] = [
                (164usize, 268435454usize),
                (16usize, 16777216usize),
                (32usize, 16777216usize),
                (97usize, 16777216usize),
                (99usize, 16777216usize),
                (129usize, 1744831011usize),
                (130usize, 1476396101usize),
                (151usize, 16777216usize),
                (154usize, 268435456usize),
                (155usize, 134217727usize),
                (157usize, 1744831011usize),
                (158usize, 1476396101usize),
                (161usize, 1996488705usize),
                (140usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (165usize, 268435454usize),
                (162usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 16usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 18usize] = [
                (166usize, 268435454usize),
                (18usize, 16777216usize),
                (34usize, 16777216usize),
                (98usize, 16777216usize),
                (100usize, 16777216usize),
                (129usize, 16777216usize),
                (130usize, 33554432usize),
                (131usize, 1744831011usize),
                (132usize, 1476396101usize),
                (149usize, 268435456usize),
                (150usize, 134217727usize),
                (156usize, 16777216usize),
                (157usize, 16777216usize),
                (158usize, 33554432usize),
                (159usize, 1744831011usize),
                (160usize, 1476396101usize),
                (162usize, 1996488705usize),
                (137usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 2usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (171usize, 268435454usize),
                (169usize, 268435454usize),
                (151usize, 268435454usize),
                (154usize, 268435422usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 8usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (172usize, 268435454usize),
                (47usize, 33554432usize),
                (139usize, 33554432usize),
                (140usize, 536870908usize),
                (141usize, 1476396101usize),
                (164usize, 33554432usize),
                (165usize, 536870908usize),
                (167usize, 1476396101usize),
                (169usize, 1979711489usize),
                (155usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 2usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (173usize, 268435454usize),
                (170usize, 268435454usize),
                (149usize, 268435422usize),
                (156usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 10usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 12usize] = [
                (174usize, 268435454usize),
                (48usize, 33554432usize),
                (136usize, 33554432usize),
                (137usize, 536870908usize),
                (141usize, 33554432usize),
                (142usize, 1476396101usize),
                (163usize, 536870908usize),
                (166usize, 33554432usize),
                (167usize, 33554432usize),
                (168usize, 1476396101usize),
                (170usize, 1979711489usize),
                (150usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (182usize, 268435454usize),
                (179usize, 268435454usize),
                (181usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 6usize),
                (0usize, 2usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 9usize] = [
                (183usize, 268435454usize),
                (20usize, 16777216usize),
                (36usize, 16777216usize),
                (101usize, 16777216usize),
                (175usize, 1744831011usize),
                (176usize, 1476396101usize),
                (179usize, 1996488705usize),
                (55usize, 16777216usize),
                (181usize, 1996488705usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (185usize, 268435454usize),
                (180usize, 268435454usize),
                (184usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 8usize),
                (0usize, 2usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 11usize] = [
                (186usize, 268435454usize),
                (22usize, 16777216usize),
                (38usize, 16777216usize),
                (102usize, 16777216usize),
                (175usize, 16777216usize),
                (176usize, 33554432usize),
                (177usize, 1744831011usize),
                (178usize, 1476396101usize),
                (180usize, 1996488705usize),
                (56usize, 16777216usize),
                (184usize, 1996488705usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (536870876usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (195usize, 268435454usize),
                (189usize, 268435454usize),
                (193usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (196usize, 268435454usize),
                (190usize, 268435454usize),
                (194usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (805306330usize, 0usize),
                (0usize, 1usize),
                (0usize, 6usize),
                (0usize, 3usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (197usize, 268435454usize),
                (49usize, 1048576usize),
                (185usize, 1048576usize),
                (186usize, 268435456usize),
                (187usize, 1744830499usize),
                (189usize, 2012217345usize),
                (190usize, 2004877313usize),
                (36usize, 1048576usize),
                (193usize, 2012217345usize),
                (194usize, 2004877313usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (536870876usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (200usize, 268435454usize),
                (191usize, 268435454usize),
                (198usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (201usize, 268435454usize),
                (192usize, 268435454usize),
                (199usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (805306330usize, 0usize),
                (0usize, 1usize),
                (0usize, 7usize),
                (0usize, 3usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 11usize] = [
                (202usize, 268435454usize),
                (50usize, 1048576usize),
                (182usize, 1048576usize),
                (183usize, 268435456usize),
                (187usize, 1048576usize),
                (188usize, 1744830499usize),
                (191usize, 2012217345usize),
                (192usize, 2004877313usize),
                (38usize, 1048576usize),
                (198usize, 2012217345usize),
                (199usize, 2004877313usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (209usize, 268435454usize),
                (207usize, 268435454usize),
                (185usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 12usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 14usize] = [
                (210usize, 268435454usize),
                (20usize, 16777216usize),
                (36usize, 16777216usize),
                (101usize, 16777216usize),
                (103usize, 16777216usize),
                (175usize, 1744831011usize),
                (176usize, 1476396101usize),
                (197usize, 16777216usize),
                (200usize, 268435456usize),
                (201usize, 134217727usize),
                (203usize, 1744831011usize),
                (204usize, 1476396101usize),
                (207usize, 1996488705usize),
                (186usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (211usize, 268435454usize),
                (208usize, 268435454usize),
                (182usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 16usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 18usize] = [
                (212usize, 268435454usize),
                (22usize, 16777216usize),
                (38usize, 16777216usize),
                (102usize, 16777216usize),
                (104usize, 16777216usize),
                (175usize, 16777216usize),
                (176usize, 33554432usize),
                (177usize, 1744831011usize),
                (178usize, 1476396101usize),
                (195usize, 268435456usize),
                (196usize, 134217727usize),
                (202usize, 16777216usize),
                (203usize, 16777216usize),
                (204usize, 33554432usize),
                (205usize, 1744831011usize),
                (206usize, 1476396101usize),
                (208usize, 1996488705usize),
                (183usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 2usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (217usize, 268435454usize),
                (215usize, 268435454usize),
                (197usize, 268435454usize),
                (200usize, 268435422usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 8usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (218usize, 268435454usize),
                (49usize, 33554432usize),
                (185usize, 33554432usize),
                (186usize, 536870908usize),
                (187usize, 1476396101usize),
                (210usize, 33554432usize),
                (211usize, 536870908usize),
                (213usize, 1476396101usize),
                (215usize, 1979711489usize),
                (201usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 2usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (219usize, 268435454usize),
                (216usize, 268435454usize),
                (195usize, 268435422usize),
                (202usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 10usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 12usize] = [
                (220usize, 268435454usize),
                (50usize, 33554432usize),
                (182usize, 33554432usize),
                (183usize, 536870908usize),
                (187usize, 33554432usize),
                (188usize, 1476396101usize),
                (209usize, 536870908usize),
                (212usize, 33554432usize),
                (213usize, 33554432usize),
                (214usize, 1476396101usize),
                (216usize, 1979711489usize),
                (196usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (228usize, 268435454usize),
                (225usize, 268435454usize),
                (227usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 6usize),
                (0usize, 2usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 9usize] = [
                (229usize, 268435454usize),
                (24usize, 16777216usize),
                (40usize, 16777216usize),
                (105usize, 16777216usize),
                (221usize, 1744831011usize),
                (222usize, 1476396101usize),
                (225usize, 1996488705usize),
                (61usize, 16777216usize),
                (227usize, 1996488705usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (231usize, 268435454usize),
                (226usize, 268435454usize),
                (230usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 8usize),
                (0usize, 2usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 11usize] = [
                (232usize, 268435454usize),
                (26usize, 16777216usize),
                (42usize, 16777216usize),
                (106usize, 16777216usize),
                (221usize, 16777216usize),
                (222usize, 33554432usize),
                (223usize, 1744831011usize),
                (224usize, 1476396101usize),
                (226usize, 1996488705usize),
                (62usize, 16777216usize),
                (230usize, 1996488705usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (536870876usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (241usize, 268435454usize),
                (235usize, 268435454usize),
                (239usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (242usize, 268435454usize),
                (236usize, 268435454usize),
                (240usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (805306330usize, 0usize),
                (0usize, 1usize),
                (0usize, 6usize),
                (0usize, 3usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (243usize, 268435454usize),
                (51usize, 1048576usize),
                (231usize, 1048576usize),
                (232usize, 268435456usize),
                (233usize, 1744830499usize),
                (235usize, 2012217345usize),
                (236usize, 2004877313usize),
                (40usize, 1048576usize),
                (239usize, 2012217345usize),
                (240usize, 2004877313usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (536870876usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (246usize, 268435454usize),
                (237usize, 268435454usize),
                (244usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (247usize, 268435454usize),
                (238usize, 268435454usize),
                (245usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (805306330usize, 0usize),
                (0usize, 1usize),
                (0usize, 7usize),
                (0usize, 3usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 11usize] = [
                (248usize, 268435454usize),
                (52usize, 1048576usize),
                (228usize, 1048576usize),
                (229usize, 268435456usize),
                (233usize, 1048576usize),
                (234usize, 1744830499usize),
                (237usize, 2012217345usize),
                (238usize, 2004877313usize),
                (42usize, 1048576usize),
                (244usize, 2012217345usize),
                (245usize, 2004877313usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (255usize, 268435454usize),
                (253usize, 268435454usize),
                (231usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 12usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 14usize] = [
                (256usize, 268435454usize),
                (24usize, 16777216usize),
                (40usize, 16777216usize),
                (105usize, 16777216usize),
                (107usize, 16777216usize),
                (221usize, 1744831011usize),
                (222usize, 1476396101usize),
                (243usize, 16777216usize),
                (246usize, 268435456usize),
                (247usize, 134217727usize),
                (249usize, 1744831011usize),
                (250usize, 1476396101usize),
                (253usize, 1996488705usize),
                (232usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (257usize, 268435454usize),
                (254usize, 268435454usize),
                (228usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 16usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 18usize] = [
                (258usize, 268435454usize),
                (26usize, 16777216usize),
                (42usize, 16777216usize),
                (106usize, 16777216usize),
                (108usize, 16777216usize),
                (221usize, 16777216usize),
                (222usize, 33554432usize),
                (223usize, 1744831011usize),
                (224usize, 1476396101usize),
                (241usize, 268435456usize),
                (242usize, 134217727usize),
                (248usize, 16777216usize),
                (249usize, 16777216usize),
                (250usize, 33554432usize),
                (251usize, 1744831011usize),
                (252usize, 1476396101usize),
                (254usize, 1996488705usize),
                (229usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 2usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (263usize, 268435454usize),
                (261usize, 268435454usize),
                (243usize, 268435454usize),
                (246usize, 268435422usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 8usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (264usize, 268435454usize),
                (51usize, 33554432usize),
                (231usize, 33554432usize),
                (232usize, 536870908usize),
                (233usize, 1476396101usize),
                (256usize, 33554432usize),
                (257usize, 536870908usize),
                (259usize, 1476396101usize),
                (261usize, 1979711489usize),
                (247usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 2usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (265usize, 268435454usize),
                (262usize, 268435454usize),
                (241usize, 268435422usize),
                (248usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 10usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 12usize] = [
                (266usize, 268435454usize),
                (52usize, 33554432usize),
                (228usize, 33554432usize),
                (229usize, 536870908usize),
                (233usize, 33554432usize),
                (234usize, 1476396101usize),
                (255usize, 536870908usize),
                (258usize, 33554432usize),
                (259usize, 33554432usize),
                (260usize, 1476396101usize),
                (262usize, 1979711489usize),
                (242usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (274usize, 268435454usize),
                (271usize, 268435454usize),
                (273usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 6usize),
                (0usize, 2usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 9usize] = [
                (275usize, 268435454usize),
                (28usize, 16777216usize),
                (44usize, 16777216usize),
                (109usize, 16777216usize),
                (267usize, 1744831011usize),
                (268usize, 1476396101usize),
                (271usize, 1996488705usize),
                (57usize, 16777216usize),
                (273usize, 1996488705usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (277usize, 268435454usize),
                (272usize, 268435454usize),
                (276usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 8usize),
                (0usize, 2usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 11usize] = [
                (278usize, 268435454usize),
                (30usize, 16777216usize),
                (46usize, 16777216usize),
                (110usize, 16777216usize),
                (267usize, 16777216usize),
                (268usize, 33554432usize),
                (269usize, 1744831011usize),
                (270usize, 1476396101usize),
                (272usize, 1996488705usize),
                (58usize, 16777216usize),
                (276usize, 1996488705usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (536870876usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (287usize, 268435454usize),
                (281usize, 268435454usize),
                (285usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (288usize, 268435454usize),
                (282usize, 268435454usize),
                (286usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (805306330usize, 0usize),
                (0usize, 1usize),
                (0usize, 6usize),
                (0usize, 3usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (289usize, 268435454usize),
                (53usize, 1048576usize),
                (277usize, 1048576usize),
                (278usize, 268435456usize),
                (279usize, 1744830499usize),
                (281usize, 2012217345usize),
                (282usize, 2004877313usize),
                (44usize, 1048576usize),
                (285usize, 2012217345usize),
                (286usize, 2004877313usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (536870876usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (292usize, 268435454usize),
                (283usize, 268435454usize),
                (290usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (293usize, 268435454usize),
                (284usize, 268435454usize),
                (291usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (805306330usize, 0usize),
                (0usize, 1usize),
                (0usize, 7usize),
                (0usize, 3usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 11usize] = [
                (294usize, 268435454usize),
                (54usize, 1048576usize),
                (274usize, 1048576usize),
                (275usize, 268435456usize),
                (279usize, 1048576usize),
                (280usize, 1744830499usize),
                (283usize, 2012217345usize),
                (284usize, 2004877313usize),
                (46usize, 1048576usize),
                (290usize, 2012217345usize),
                (291usize, 2004877313usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (301usize, 268435454usize),
                (299usize, 268435454usize),
                (277usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 12usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 14usize] = [
                (302usize, 268435454usize),
                (28usize, 16777216usize),
                (44usize, 16777216usize),
                (109usize, 16777216usize),
                (111usize, 16777216usize),
                (267usize, 1744831011usize),
                (268usize, 1476396101usize),
                (289usize, 16777216usize),
                (292usize, 268435456usize),
                (293usize, 134217727usize),
                (295usize, 1744831011usize),
                (296usize, 1476396101usize),
                (299usize, 1996488705usize),
                (278usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (303usize, 268435454usize),
                (300usize, 268435454usize),
                (274usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 16usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 18usize] = [
                (304usize, 268435454usize),
                (30usize, 16777216usize),
                (46usize, 16777216usize),
                (110usize, 16777216usize),
                (112usize, 16777216usize),
                (267usize, 16777216usize),
                (268usize, 33554432usize),
                (269usize, 1744831011usize),
                (270usize, 1476396101usize),
                (287usize, 268435456usize),
                (288usize, 134217727usize),
                (294usize, 16777216usize),
                (295usize, 16777216usize),
                (296usize, 33554432usize),
                (297usize, 1744831011usize),
                (298usize, 1476396101usize),
                (300usize, 1996488705usize),
                (275usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 2usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (309usize, 268435454usize),
                (307usize, 268435454usize),
                (289usize, 268435454usize),
                (292usize, 268435422usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 8usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (310usize, 268435454usize),
                (53usize, 33554432usize),
                (277usize, 33554432usize),
                (278usize, 536870908usize),
                (279usize, 1476396101usize),
                (302usize, 33554432usize),
                (303usize, 536870908usize),
                (305usize, 1476396101usize),
                (307usize, 1979711489usize),
                (293usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 2usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (311usize, 268435454usize),
                (308usize, 268435454usize),
                (287usize, 268435422usize),
                (294usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 10usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 12usize] = [
                (312usize, 268435454usize),
                (54usize, 33554432usize),
                (274usize, 33554432usize),
                (275usize, 536870908usize),
                (279usize, 33554432usize),
                (280usize, 1476396101usize),
                (301usize, 536870908usize),
                (304usize, 33554432usize),
                (305usize, 33554432usize),
                (306usize, 1476396101usize),
                (308usize, 1979711489usize),
                (288usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (319usize, 268435454usize),
                (317usize, 268435454usize),
                (302usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 17usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 19usize] = [
                (320usize, 268435454usize),
                (16usize, 16777216usize),
                (32usize, 16777216usize),
                (97usize, 16777216usize),
                (99usize, 16777216usize),
                (113usize, 16777216usize),
                (129usize, 1744831011usize),
                (130usize, 1476396101usize),
                (151usize, 16777216usize),
                (154usize, 268435456usize),
                (155usize, 134217727usize),
                (157usize, 1744831011usize),
                (158usize, 1476396101usize),
                (218usize, 16777216usize),
                (219usize, 536870908usize),
                (313usize, 1744831011usize),
                (314usize, 1476396101usize),
                (317usize, 1996488705usize),
                (303usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (321usize, 268435454usize),
                (318usize, 268435454usize),
                (304usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 23usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 25usize] = [
                (322usize, 268435454usize),
                (18usize, 16777216usize),
                (34usize, 16777216usize),
                (98usize, 16777216usize),
                (100usize, 16777216usize),
                (114usize, 16777216usize),
                (129usize, 16777216usize),
                (130usize, 33554432usize),
                (131usize, 1744831011usize),
                (132usize, 1476396101usize),
                (149usize, 268435456usize),
                (150usize, 134217727usize),
                (156usize, 16777216usize),
                (157usize, 16777216usize),
                (158usize, 33554432usize),
                (159usize, 1744831011usize),
                (160usize, 1476396101usize),
                (217usize, 536870908usize),
                (220usize, 16777216usize),
                (313usize, 16777216usize),
                (314usize, 33554432usize),
                (315usize, 1744831011usize),
                (316usize, 1476396101usize),
                (318usize, 1996488705usize),
                (301usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (536870876usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (331usize, 268435454usize),
                (325usize, 268435454usize),
                (329usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (332usize, 268435454usize),
                (326usize, 268435454usize),
                (330usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (805306330usize, 0usize),
                (0usize, 1usize),
                (0usize, 12usize),
                (0usize, 4usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 17usize] = [
                (333usize, 268435454usize),
                (51usize, 1048576usize),
                (231usize, 1048576usize),
                (232usize, 268435456usize),
                (233usize, 1744830499usize),
                (256usize, 1048576usize),
                (257usize, 268435456usize),
                (259usize, 1744830499usize),
                (321usize, 1048576usize),
                (322usize, 268435456usize),
                (323usize, 1744830499usize),
                (325usize, 2012217345usize),
                (326usize, 2004877313usize),
                (218usize, 1048576usize),
                (219usize, 536870912usize),
                (329usize, 2012217345usize),
                (330usize, 2004877313usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (536870876usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (336usize, 268435454usize),
                (327usize, 268435454usize),
                (334usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (337usize, 268435454usize),
                (328usize, 268435454usize),
                (335usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (805306330usize, 0usize),
                (0usize, 1usize),
                (0usize, 15usize),
                (0usize, 4usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 20usize] = [
                (338usize, 268435454usize),
                (52usize, 1048576usize),
                (228usize, 1048576usize),
                (229usize, 268435456usize),
                (233usize, 1048576usize),
                (234usize, 1744830499usize),
                (255usize, 268435456usize),
                (258usize, 1048576usize),
                (259usize, 1048576usize),
                (260usize, 1744830499usize),
                (319usize, 1048576usize),
                (320usize, 268435456usize),
                (323usize, 1048576usize),
                (324usize, 1744830499usize),
                (327usize, 2012217345usize),
                (328usize, 2004877313usize),
                (217usize, 536870912usize),
                (220usize, 1048576usize),
                (334usize, 2012217345usize),
                (335usize, 2004877313usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (345usize, 268435454usize),
                (343usize, 268435454usize),
                (321usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 23usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 25usize] = [
                (346usize, 268435454usize),
                (16usize, 16777216usize),
                (32usize, 16777216usize),
                (97usize, 16777216usize),
                (99usize, 16777216usize),
                (113usize, 16777216usize),
                (115usize, 16777216usize),
                (129usize, 1744831011usize),
                (130usize, 1476396101usize),
                (151usize, 16777216usize),
                (154usize, 268435456usize),
                (155usize, 134217727usize),
                (157usize, 1744831011usize),
                (158usize, 1476396101usize),
                (218usize, 16777216usize),
                (219usize, 536870908usize),
                (313usize, 1744831011usize),
                (314usize, 1476396101usize),
                (333usize, 16777216usize),
                (336usize, 268435456usize),
                (337usize, 134217727usize),
                (339usize, 1744831011usize),
                (340usize, 1476396101usize),
                (343usize, 1996488705usize),
                (322usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (347usize, 268435454usize),
                (344usize, 268435454usize),
                (319usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 31usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 33usize] = [
                (348usize, 268435454usize),
                (18usize, 16777216usize),
                (34usize, 16777216usize),
                (98usize, 16777216usize),
                (100usize, 16777216usize),
                (114usize, 16777216usize),
                (116usize, 16777216usize),
                (129usize, 16777216usize),
                (130usize, 33554432usize),
                (131usize, 1744831011usize),
                (132usize, 1476396101usize),
                (149usize, 268435456usize),
                (150usize, 134217727usize),
                (156usize, 16777216usize),
                (157usize, 16777216usize),
                (158usize, 33554432usize),
                (159usize, 1744831011usize),
                (160usize, 1476396101usize),
                (217usize, 536870908usize),
                (220usize, 16777216usize),
                (313usize, 16777216usize),
                (314usize, 33554432usize),
                (315usize, 1744831011usize),
                (316usize, 1476396101usize),
                (331usize, 268435456usize),
                (332usize, 134217727usize),
                (338usize, 16777216usize),
                (339usize, 16777216usize),
                (340usize, 33554432usize),
                (341usize, 1744831011usize),
                (342usize, 1476396101usize),
                (344usize, 1996488705usize),
                (320usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 2usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (353usize, 268435454usize),
                (351usize, 268435454usize),
                (333usize, 268435454usize),
                (336usize, 268435422usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 14usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 16usize] = [
                (354usize, 268435454usize),
                (51usize, 33554432usize),
                (231usize, 33554432usize),
                (232usize, 536870908usize),
                (233usize, 1476396101usize),
                (256usize, 33554432usize),
                (257usize, 536870908usize),
                (259usize, 1476396101usize),
                (321usize, 33554432usize),
                (322usize, 536870908usize),
                (323usize, 1476396101usize),
                (346usize, 33554432usize),
                (347usize, 536870908usize),
                (349usize, 1476396101usize),
                (351usize, 1979711489usize),
                (337usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 2usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (355usize, 268435454usize),
                (352usize, 268435454usize),
                (331usize, 268435422usize),
                (338usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 18usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 20usize] = [
                (356usize, 268435454usize),
                (52usize, 33554432usize),
                (228usize, 33554432usize),
                (229usize, 536870908usize),
                (233usize, 33554432usize),
                (234usize, 1476396101usize),
                (255usize, 536870908usize),
                (258usize, 33554432usize),
                (259usize, 33554432usize),
                (260usize, 1476396101usize),
                (319usize, 33554432usize),
                (320usize, 536870908usize),
                (323usize, 33554432usize),
                (324usize, 1476396101usize),
                (345usize, 536870908usize),
                (348usize, 33554432usize),
                (349usize, 33554432usize),
                (350usize, 1476396101usize),
                (352usize, 1979711489usize),
                (332usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (363usize, 268435454usize),
                (361usize, 268435454usize),
                (164usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 17usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 19usize] = [
                (364usize, 268435454usize),
                (20usize, 16777216usize),
                (36usize, 16777216usize),
                (101usize, 16777216usize),
                (103usize, 16777216usize),
                (117usize, 16777216usize),
                (175usize, 1744831011usize),
                (176usize, 1476396101usize),
                (197usize, 16777216usize),
                (200usize, 268435456usize),
                (201usize, 134217727usize),
                (203usize, 1744831011usize),
                (204usize, 1476396101usize),
                (264usize, 16777216usize),
                (265usize, 536870908usize),
                (357usize, 1744831011usize),
                (358usize, 1476396101usize),
                (361usize, 1996488705usize),
                (165usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (365usize, 268435454usize),
                (362usize, 268435454usize),
                (166usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 23usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 25usize] = [
                (366usize, 268435454usize),
                (22usize, 16777216usize),
                (38usize, 16777216usize),
                (102usize, 16777216usize),
                (104usize, 16777216usize),
                (118usize, 16777216usize),
                (175usize, 16777216usize),
                (176usize, 33554432usize),
                (177usize, 1744831011usize),
                (178usize, 1476396101usize),
                (195usize, 268435456usize),
                (196usize, 134217727usize),
                (202usize, 16777216usize),
                (203usize, 16777216usize),
                (204usize, 33554432usize),
                (205usize, 1744831011usize),
                (206usize, 1476396101usize),
                (263usize, 536870908usize),
                (266usize, 16777216usize),
                (357usize, 16777216usize),
                (358usize, 33554432usize),
                (359usize, 1744831011usize),
                (360usize, 1476396101usize),
                (362usize, 1996488705usize),
                (163usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (536870876usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (375usize, 268435454usize),
                (369usize, 268435454usize),
                (373usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (376usize, 268435454usize),
                (370usize, 268435454usize),
                (374usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (805306330usize, 0usize),
                (0usize, 1usize),
                (0usize, 12usize),
                (0usize, 4usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 17usize] = [
                (377usize, 268435454usize),
                (53usize, 1048576usize),
                (277usize, 1048576usize),
                (278usize, 268435456usize),
                (279usize, 1744830499usize),
                (302usize, 1048576usize),
                (303usize, 268435456usize),
                (305usize, 1744830499usize),
                (365usize, 1048576usize),
                (366usize, 268435456usize),
                (367usize, 1744830499usize),
                (369usize, 2012217345usize),
                (370usize, 2004877313usize),
                (264usize, 1048576usize),
                (265usize, 536870912usize),
                (373usize, 2012217345usize),
                (374usize, 2004877313usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (536870876usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (380usize, 268435454usize),
                (371usize, 268435454usize),
                (378usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (381usize, 268435454usize),
                (372usize, 268435454usize),
                (379usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (805306330usize, 0usize),
                (0usize, 1usize),
                (0usize, 15usize),
                (0usize, 4usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 20usize] = [
                (382usize, 268435454usize),
                (54usize, 1048576usize),
                (274usize, 1048576usize),
                (275usize, 268435456usize),
                (279usize, 1048576usize),
                (280usize, 1744830499usize),
                (301usize, 268435456usize),
                (304usize, 1048576usize),
                (305usize, 1048576usize),
                (306usize, 1744830499usize),
                (363usize, 1048576usize),
                (364usize, 268435456usize),
                (367usize, 1048576usize),
                (368usize, 1744830499usize),
                (371usize, 2012217345usize),
                (372usize, 2004877313usize),
                (263usize, 536870912usize),
                (266usize, 1048576usize),
                (378usize, 2012217345usize),
                (379usize, 2004877313usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (389usize, 268435454usize),
                (387usize, 268435454usize),
                (365usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 23usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 25usize] = [
                (390usize, 268435454usize),
                (20usize, 16777216usize),
                (36usize, 16777216usize),
                (101usize, 16777216usize),
                (103usize, 16777216usize),
                (117usize, 16777216usize),
                (119usize, 16777216usize),
                (175usize, 1744831011usize),
                (176usize, 1476396101usize),
                (197usize, 16777216usize),
                (200usize, 268435456usize),
                (201usize, 134217727usize),
                (203usize, 1744831011usize),
                (204usize, 1476396101usize),
                (264usize, 16777216usize),
                (265usize, 536870908usize),
                (357usize, 1744831011usize),
                (358usize, 1476396101usize),
                (377usize, 16777216usize),
                (380usize, 268435456usize),
                (381usize, 134217727usize),
                (383usize, 1744831011usize),
                (384usize, 1476396101usize),
                (387usize, 1996488705usize),
                (366usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (391usize, 268435454usize),
                (388usize, 268435454usize),
                (363usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 31usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 33usize] = [
                (392usize, 268435454usize),
                (22usize, 16777216usize),
                (38usize, 16777216usize),
                (102usize, 16777216usize),
                (104usize, 16777216usize),
                (118usize, 16777216usize),
                (120usize, 16777216usize),
                (175usize, 16777216usize),
                (176usize, 33554432usize),
                (177usize, 1744831011usize),
                (178usize, 1476396101usize),
                (195usize, 268435456usize),
                (196usize, 134217727usize),
                (202usize, 16777216usize),
                (203usize, 16777216usize),
                (204usize, 33554432usize),
                (205usize, 1744831011usize),
                (206usize, 1476396101usize),
                (263usize, 536870908usize),
                (266usize, 16777216usize),
                (357usize, 16777216usize),
                (358usize, 33554432usize),
                (359usize, 1744831011usize),
                (360usize, 1476396101usize),
                (375usize, 268435456usize),
                (376usize, 134217727usize),
                (382usize, 16777216usize),
                (383usize, 16777216usize),
                (384usize, 33554432usize),
                (385usize, 1744831011usize),
                (386usize, 1476396101usize),
                (388usize, 1996488705usize),
                (364usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 2usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (397usize, 268435454usize),
                (395usize, 268435454usize),
                (377usize, 268435454usize),
                (380usize, 268435422usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 14usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 16usize] = [
                (398usize, 268435454usize),
                (53usize, 33554432usize),
                (277usize, 33554432usize),
                (278usize, 536870908usize),
                (279usize, 1476396101usize),
                (302usize, 33554432usize),
                (303usize, 536870908usize),
                (305usize, 1476396101usize),
                (365usize, 33554432usize),
                (366usize, 536870908usize),
                (367usize, 1476396101usize),
                (390usize, 33554432usize),
                (391usize, 536870908usize),
                (393usize, 1476396101usize),
                (395usize, 1979711489usize),
                (381usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 2usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (399usize, 268435454usize),
                (396usize, 268435454usize),
                (375usize, 268435422usize),
                (382usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 18usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 20usize] = [
                (400usize, 268435454usize),
                (54usize, 33554432usize),
                (274usize, 33554432usize),
                (275usize, 536870908usize),
                (279usize, 33554432usize),
                (280usize, 1476396101usize),
                (301usize, 536870908usize),
                (304usize, 33554432usize),
                (305usize, 33554432usize),
                (306usize, 1476396101usize),
                (363usize, 33554432usize),
                (364usize, 536870908usize),
                (367usize, 33554432usize),
                (368usize, 1476396101usize),
                (389usize, 536870908usize),
                (392usize, 33554432usize),
                (393usize, 33554432usize),
                (394usize, 1476396101usize),
                (396usize, 1979711489usize),
                (376usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (407usize, 268435454usize),
                (405usize, 268435454usize),
                (210usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 17usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 19usize] = [
                (408usize, 268435454usize),
                (24usize, 16777216usize),
                (40usize, 16777216usize),
                (105usize, 16777216usize),
                (107usize, 16777216usize),
                (121usize, 16777216usize),
                (221usize, 1744831011usize),
                (222usize, 1476396101usize),
                (243usize, 16777216usize),
                (246usize, 268435456usize),
                (247usize, 134217727usize),
                (249usize, 1744831011usize),
                (250usize, 1476396101usize),
                (310usize, 16777216usize),
                (311usize, 536870908usize),
                (401usize, 1744831011usize),
                (402usize, 1476396101usize),
                (405usize, 1996488705usize),
                (211usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (409usize, 268435454usize),
                (406usize, 268435454usize),
                (212usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 23usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 25usize] = [
                (410usize, 268435454usize),
                (26usize, 16777216usize),
                (42usize, 16777216usize),
                (106usize, 16777216usize),
                (108usize, 16777216usize),
                (122usize, 16777216usize),
                (221usize, 16777216usize),
                (222usize, 33554432usize),
                (223usize, 1744831011usize),
                (224usize, 1476396101usize),
                (241usize, 268435456usize),
                (242usize, 134217727usize),
                (248usize, 16777216usize),
                (249usize, 16777216usize),
                (250usize, 33554432usize),
                (251usize, 1744831011usize),
                (252usize, 1476396101usize),
                (309usize, 536870908usize),
                (312usize, 16777216usize),
                (401usize, 16777216usize),
                (402usize, 33554432usize),
                (403usize, 1744831011usize),
                (404usize, 1476396101usize),
                (406usize, 1996488705usize),
                (209usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (536870876usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (419usize, 268435454usize),
                (413usize, 268435454usize),
                (417usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (420usize, 268435454usize),
                (414usize, 268435454usize),
                (418usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (805306330usize, 0usize),
                (0usize, 1usize),
                (0usize, 12usize),
                (0usize, 4usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 17usize] = [
                (421usize, 268435454usize),
                (47usize, 1048576usize),
                (139usize, 1048576usize),
                (140usize, 268435456usize),
                (141usize, 1744830499usize),
                (164usize, 1048576usize),
                (165usize, 268435456usize),
                (167usize, 1744830499usize),
                (409usize, 1048576usize),
                (410usize, 268435456usize),
                (411usize, 1744830499usize),
                (413usize, 2012217345usize),
                (414usize, 2004877313usize),
                (310usize, 1048576usize),
                (311usize, 536870912usize),
                (417usize, 2012217345usize),
                (418usize, 2004877313usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (536870876usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (424usize, 268435454usize),
                (415usize, 268435454usize),
                (422usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (425usize, 268435454usize),
                (416usize, 268435454usize),
                (423usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (805306330usize, 0usize),
                (0usize, 1usize),
                (0usize, 15usize),
                (0usize, 4usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 20usize] = [
                (426usize, 268435454usize),
                (48usize, 1048576usize),
                (136usize, 1048576usize),
                (137usize, 268435456usize),
                (141usize, 1048576usize),
                (142usize, 1744830499usize),
                (163usize, 268435456usize),
                (166usize, 1048576usize),
                (167usize, 1048576usize),
                (168usize, 1744830499usize),
                (407usize, 1048576usize),
                (408usize, 268435456usize),
                (411usize, 1048576usize),
                (412usize, 1744830499usize),
                (415usize, 2012217345usize),
                (416usize, 2004877313usize),
                (309usize, 536870912usize),
                (312usize, 1048576usize),
                (422usize, 2012217345usize),
                (423usize, 2004877313usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (433usize, 268435454usize),
                (431usize, 268435454usize),
                (409usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 23usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 25usize] = [
                (434usize, 268435454usize),
                (24usize, 16777216usize),
                (40usize, 16777216usize),
                (105usize, 16777216usize),
                (107usize, 16777216usize),
                (121usize, 16777216usize),
                (123usize, 16777216usize),
                (221usize, 1744831011usize),
                (222usize, 1476396101usize),
                (243usize, 16777216usize),
                (246usize, 268435456usize),
                (247usize, 134217727usize),
                (249usize, 1744831011usize),
                (250usize, 1476396101usize),
                (310usize, 16777216usize),
                (311usize, 536870908usize),
                (401usize, 1744831011usize),
                (402usize, 1476396101usize),
                (421usize, 16777216usize),
                (424usize, 268435456usize),
                (425usize, 134217727usize),
                (427usize, 1744831011usize),
                (428usize, 1476396101usize),
                (431usize, 1996488705usize),
                (410usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (435usize, 268435454usize),
                (432usize, 268435454usize),
                (407usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 31usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 33usize] = [
                (436usize, 268435454usize),
                (26usize, 16777216usize),
                (42usize, 16777216usize),
                (106usize, 16777216usize),
                (108usize, 16777216usize),
                (122usize, 16777216usize),
                (124usize, 16777216usize),
                (221usize, 16777216usize),
                (222usize, 33554432usize),
                (223usize, 1744831011usize),
                (224usize, 1476396101usize),
                (241usize, 268435456usize),
                (242usize, 134217727usize),
                (248usize, 16777216usize),
                (249usize, 16777216usize),
                (250usize, 33554432usize),
                (251usize, 1744831011usize),
                (252usize, 1476396101usize),
                (309usize, 536870908usize),
                (312usize, 16777216usize),
                (401usize, 16777216usize),
                (402usize, 33554432usize),
                (403usize, 1744831011usize),
                (404usize, 1476396101usize),
                (419usize, 268435456usize),
                (420usize, 134217727usize),
                (426usize, 16777216usize),
                (427usize, 16777216usize),
                (428usize, 33554432usize),
                (429usize, 1744831011usize),
                (430usize, 1476396101usize),
                (432usize, 1996488705usize),
                (408usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 2usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (441usize, 268435454usize),
                (439usize, 268435454usize),
                (421usize, 268435454usize),
                (424usize, 268435422usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 14usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 16usize] = [
                (442usize, 268435454usize),
                (47usize, 33554432usize),
                (139usize, 33554432usize),
                (140usize, 536870908usize),
                (141usize, 1476396101usize),
                (164usize, 33554432usize),
                (165usize, 536870908usize),
                (167usize, 1476396101usize),
                (409usize, 33554432usize),
                (410usize, 536870908usize),
                (411usize, 1476396101usize),
                (434usize, 33554432usize),
                (435usize, 536870908usize),
                (437usize, 1476396101usize),
                (439usize, 1979711489usize),
                (425usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 2usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (443usize, 268435454usize),
                (440usize, 268435454usize),
                (419usize, 268435422usize),
                (426usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 18usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 20usize] = [
                (444usize, 268435454usize),
                (48usize, 33554432usize),
                (136usize, 33554432usize),
                (137usize, 536870908usize),
                (141usize, 33554432usize),
                (142usize, 1476396101usize),
                (163usize, 536870908usize),
                (166usize, 33554432usize),
                (167usize, 33554432usize),
                (168usize, 1476396101usize),
                (407usize, 33554432usize),
                (408usize, 536870908usize),
                (411usize, 33554432usize),
                (412usize, 1476396101usize),
                (433usize, 536870908usize),
                (436usize, 33554432usize),
                (437usize, 33554432usize),
                (438usize, 1476396101usize),
                (440usize, 1979711489usize),
                (420usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (451usize, 268435454usize),
                (449usize, 268435454usize),
                (256usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 17usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 19usize] = [
                (452usize, 268435454usize),
                (28usize, 16777216usize),
                (44usize, 16777216usize),
                (109usize, 16777216usize),
                (111usize, 16777216usize),
                (125usize, 16777216usize),
                (172usize, 16777216usize),
                (173usize, 536870908usize),
                (267usize, 1744831011usize),
                (268usize, 1476396101usize),
                (289usize, 16777216usize),
                (292usize, 268435456usize),
                (293usize, 134217727usize),
                (295usize, 1744831011usize),
                (296usize, 1476396101usize),
                (445usize, 1744831011usize),
                (446usize, 1476396101usize),
                (449usize, 1996488705usize),
                (257usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (453usize, 268435454usize),
                (450usize, 268435454usize),
                (258usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 23usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 25usize] = [
                (454usize, 268435454usize),
                (30usize, 16777216usize),
                (46usize, 16777216usize),
                (110usize, 16777216usize),
                (112usize, 16777216usize),
                (126usize, 16777216usize),
                (171usize, 536870908usize),
                (174usize, 16777216usize),
                (267usize, 16777216usize),
                (268usize, 33554432usize),
                (269usize, 1744831011usize),
                (270usize, 1476396101usize),
                (287usize, 268435456usize),
                (288usize, 134217727usize),
                (294usize, 16777216usize),
                (295usize, 16777216usize),
                (296usize, 33554432usize),
                (297usize, 1744831011usize),
                (298usize, 1476396101usize),
                (445usize, 16777216usize),
                (446usize, 33554432usize),
                (447usize, 1744831011usize),
                (448usize, 1476396101usize),
                (450usize, 1996488705usize),
                (255usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (536870876usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (463usize, 268435454usize),
                (457usize, 268435454usize),
                (461usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (464usize, 268435454usize),
                (458usize, 268435454usize),
                (462usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (805306330usize, 0usize),
                (0usize, 1usize),
                (0usize, 12usize),
                (0usize, 4usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 17usize] = [
                (465usize, 268435454usize),
                (49usize, 1048576usize),
                (185usize, 1048576usize),
                (186usize, 268435456usize),
                (187usize, 1744830499usize),
                (210usize, 1048576usize),
                (211usize, 268435456usize),
                (213usize, 1744830499usize),
                (453usize, 1048576usize),
                (454usize, 268435456usize),
                (455usize, 1744830499usize),
                (457usize, 2012217345usize),
                (458usize, 2004877313usize),
                (172usize, 1048576usize),
                (173usize, 536870912usize),
                (461usize, 2012217345usize),
                (462usize, 2004877313usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (536870876usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (468usize, 268435454usize),
                (459usize, 268435454usize),
                (466usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (469usize, 268435454usize),
                (460usize, 268435454usize),
                (467usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (805306330usize, 0usize),
                (0usize, 1usize),
                (0usize, 15usize),
                (0usize, 4usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 20usize] = [
                (470usize, 268435454usize),
                (50usize, 1048576usize),
                (182usize, 1048576usize),
                (183usize, 268435456usize),
                (187usize, 1048576usize),
                (188usize, 1744830499usize),
                (209usize, 268435456usize),
                (212usize, 1048576usize),
                (213usize, 1048576usize),
                (214usize, 1744830499usize),
                (451usize, 1048576usize),
                (452usize, 268435456usize),
                (455usize, 1048576usize),
                (456usize, 1744830499usize),
                (459usize, 2012217345usize),
                (460usize, 2004877313usize),
                (171usize, 536870912usize),
                (174usize, 1048576usize),
                (466usize, 2012217345usize),
                (467usize, 2004877313usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (477usize, 268435454usize),
                (475usize, 268435454usize),
                (453usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 23usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 25usize] = [
                (478usize, 268435454usize),
                (28usize, 16777216usize),
                (44usize, 16777216usize),
                (109usize, 16777216usize),
                (111usize, 16777216usize),
                (125usize, 16777216usize),
                (127usize, 16777216usize),
                (172usize, 16777216usize),
                (173usize, 536870908usize),
                (267usize, 1744831011usize),
                (268usize, 1476396101usize),
                (289usize, 16777216usize),
                (292usize, 268435456usize),
                (293usize, 134217727usize),
                (295usize, 1744831011usize),
                (296usize, 1476396101usize),
                (445usize, 1744831011usize),
                (446usize, 1476396101usize),
                (465usize, 16777216usize),
                (468usize, 268435456usize),
                (469usize, 134217727usize),
                (471usize, 1744831011usize),
                (472usize, 1476396101usize),
                (475usize, 1996488705usize),
                (454usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (479usize, 268435454usize),
                (476usize, 268435454usize),
                (451usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 31usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 33usize] = [
                (480usize, 268435454usize),
                (30usize, 16777216usize),
                (46usize, 16777216usize),
                (110usize, 16777216usize),
                (112usize, 16777216usize),
                (126usize, 16777216usize),
                (128usize, 16777216usize),
                (171usize, 536870908usize),
                (174usize, 16777216usize),
                (267usize, 16777216usize),
                (268usize, 33554432usize),
                (269usize, 1744831011usize),
                (270usize, 1476396101usize),
                (287usize, 268435456usize),
                (288usize, 134217727usize),
                (294usize, 16777216usize),
                (295usize, 16777216usize),
                (296usize, 33554432usize),
                (297usize, 1744831011usize),
                (298usize, 1476396101usize),
                (445usize, 16777216usize),
                (446usize, 33554432usize),
                (447usize, 1744831011usize),
                (448usize, 1476396101usize),
                (463usize, 268435456usize),
                (464usize, 134217727usize),
                (470usize, 16777216usize),
                (471usize, 16777216usize),
                (472usize, 33554432usize),
                (473usize, 1744831011usize),
                (474usize, 1476396101usize),
                (476usize, 1996488705usize),
                (452usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 2usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (485usize, 268435454usize),
                (483usize, 268435454usize),
                (465usize, 268435454usize),
                (468usize, 268435422usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 14usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 16usize] = [
                (486usize, 268435454usize),
                (49usize, 33554432usize),
                (185usize, 33554432usize),
                (186usize, 536870908usize),
                (187usize, 1476396101usize),
                (210usize, 33554432usize),
                (211usize, 536870908usize),
                (213usize, 1476396101usize),
                (453usize, 33554432usize),
                (454usize, 536870908usize),
                (455usize, 1476396101usize),
                (478usize, 33554432usize),
                (479usize, 536870908usize),
                (481usize, 1476396101usize),
                (483usize, 1979711489usize),
                (469usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 2usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (487usize, 268435454usize),
                (484usize, 268435454usize),
                (463usize, 268435422usize),
                (470usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 18usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 20usize] = [
                (488usize, 268435454usize),
                (50usize, 33554432usize),
                (182usize, 33554432usize),
                (183usize, 536870908usize),
                (187usize, 33554432usize),
                (188usize, 1476396101usize),
                (209usize, 536870908usize),
                (212usize, 33554432usize),
                (213usize, 33554432usize),
                (214usize, 1476396101usize),
                (451usize, 33554432usize),
                (452usize, 536870908usize),
                (455usize, 33554432usize),
                (456usize, 1476396101usize),
                (477usize, 536870908usize),
                (480usize, 33554432usize),
                (481usize, 33554432usize),
                (482usize, 1476396101usize),
                (484usize, 1979711489usize),
                (464usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (490usize, 268435454usize),
                (439usize, 268435454usize),
                (489usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 14usize),
                (0usize, 2usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 17usize] = [
                (491usize, 268435454usize),
                (47usize, 33554432usize),
                (139usize, 33554432usize),
                (140usize, 536870908usize),
                (141usize, 1476396101usize),
                (164usize, 33554432usize),
                (165usize, 536870908usize),
                (167usize, 1476396101usize),
                (409usize, 33554432usize),
                (410usize, 536870908usize),
                (411usize, 1476396101usize),
                (434usize, 33554432usize),
                (435usize, 536870908usize),
                (437usize, 1476396101usize),
                (439usize, 1979711489usize),
                (15usize, 33554432usize),
                (489usize, 1979711489usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (494usize, 268435454usize),
                (492usize, 268435454usize),
                (490usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 24usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 26usize] = [
                (495usize, 268435454usize),
                (16usize, 33554432usize),
                (32usize, 33554432usize),
                (97usize, 33554432usize),
                (99usize, 33554432usize),
                (113usize, 33554432usize),
                (115usize, 33554432usize),
                (129usize, 1476396101usize),
                (130usize, 939526281usize),
                (151usize, 33554432usize),
                (154usize, 536870912usize),
                (155usize, 268435454usize),
                (157usize, 1476396101usize),
                (158usize, 939526281usize),
                (218usize, 33554432usize),
                (219usize, 1073741816usize),
                (313usize, 1476396101usize),
                (314usize, 939526281usize),
                (333usize, 33554432usize),
                (336usize, 536870912usize),
                (337usize, 268435454usize),
                (339usize, 1476396101usize),
                (340usize, 939526281usize),
                (343usize, 1979711489usize),
                (493usize, 268435454usize),
                (491usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (497usize, 268435454usize),
                (440usize, 268435454usize),
                (496usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 18usize),
                (0usize, 2usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 21usize] = [
                (498usize, 268435454usize),
                (48usize, 33554432usize),
                (136usize, 33554432usize),
                (137usize, 536870908usize),
                (141usize, 33554432usize),
                (142usize, 1476396101usize),
                (163usize, 536870908usize),
                (166usize, 33554432usize),
                (167usize, 33554432usize),
                (168usize, 1476396101usize),
                (407usize, 33554432usize),
                (408usize, 536870908usize),
                (411usize, 33554432usize),
                (412usize, 1476396101usize),
                (433usize, 536870908usize),
                (436usize, 33554432usize),
                (437usize, 33554432usize),
                (438usize, 1476396101usize),
                (440usize, 1979711489usize),
                (17usize, 33554432usize),
                (496usize, 1979711489usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (501usize, 268435454usize),
                (499usize, 268435454usize),
                (497usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 32usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 34usize] = [
                (502usize, 268435454usize),
                (18usize, 33554432usize),
                (34usize, 33554432usize),
                (98usize, 33554432usize),
                (100usize, 33554432usize),
                (114usize, 33554432usize),
                (116usize, 33554432usize),
                (129usize, 33554432usize),
                (130usize, 67108864usize),
                (131usize, 1476396101usize),
                (132usize, 939526281usize),
                (149usize, 536870912usize),
                (150usize, 268435454usize),
                (156usize, 33554432usize),
                (157usize, 33554432usize),
                (158usize, 67108864usize),
                (159usize, 1476396101usize),
                (160usize, 939526281usize),
                (217usize, 1073741816usize),
                (220usize, 33554432usize),
                (313usize, 33554432usize),
                (314usize, 67108864usize),
                (315usize, 1476396101usize),
                (316usize, 939526281usize),
                (331usize, 536870912usize),
                (332usize, 268435454usize),
                (338usize, 33554432usize),
                (339usize, 33554432usize),
                (340usize, 67108864usize),
                (341usize, 1476396101usize),
                (342usize, 939526281usize),
                (344usize, 1979711489usize),
                (500usize, 268435454usize),
                (498usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (504usize, 268435454usize),
                (483usize, 268435454usize),
                (503usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 14usize),
                (0usize, 2usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 17usize] = [
                (505usize, 268435454usize),
                (49usize, 33554432usize),
                (185usize, 33554432usize),
                (186usize, 536870908usize),
                (187usize, 1476396101usize),
                (210usize, 33554432usize),
                (211usize, 536870908usize),
                (213usize, 1476396101usize),
                (453usize, 33554432usize),
                (454usize, 536870908usize),
                (455usize, 1476396101usize),
                (478usize, 33554432usize),
                (479usize, 536870908usize),
                (481usize, 1476396101usize),
                (483usize, 1979711489usize),
                (19usize, 33554432usize),
                (503usize, 1979711489usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (508usize, 268435454usize),
                (506usize, 268435454usize),
                (504usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 24usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 26usize] = [
                (509usize, 268435454usize),
                (20usize, 33554432usize),
                (36usize, 33554432usize),
                (101usize, 33554432usize),
                (103usize, 33554432usize),
                (117usize, 33554432usize),
                (119usize, 33554432usize),
                (175usize, 1476396101usize),
                (176usize, 939526281usize),
                (197usize, 33554432usize),
                (200usize, 536870912usize),
                (201usize, 268435454usize),
                (203usize, 1476396101usize),
                (204usize, 939526281usize),
                (264usize, 33554432usize),
                (265usize, 1073741816usize),
                (357usize, 1476396101usize),
                (358usize, 939526281usize),
                (377usize, 33554432usize),
                (380usize, 536870912usize),
                (381usize, 268435454usize),
                (383usize, 1476396101usize),
                (384usize, 939526281usize),
                (387usize, 1979711489usize),
                (507usize, 268435454usize),
                (505usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (511usize, 268435454usize),
                (484usize, 268435454usize),
                (510usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 18usize),
                (0usize, 2usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 21usize] = [
                (512usize, 268435454usize),
                (50usize, 33554432usize),
                (182usize, 33554432usize),
                (183usize, 536870908usize),
                (187usize, 33554432usize),
                (188usize, 1476396101usize),
                (209usize, 536870908usize),
                (212usize, 33554432usize),
                (213usize, 33554432usize),
                (214usize, 1476396101usize),
                (451usize, 33554432usize),
                (452usize, 536870908usize),
                (455usize, 33554432usize),
                (456usize, 1476396101usize),
                (477usize, 536870908usize),
                (480usize, 33554432usize),
                (481usize, 33554432usize),
                (482usize, 1476396101usize),
                (484usize, 1979711489usize),
                (21usize, 33554432usize),
                (510usize, 1979711489usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (515usize, 268435454usize),
                (513usize, 268435454usize),
                (511usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 32usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 34usize] = [
                (516usize, 268435454usize),
                (22usize, 33554432usize),
                (38usize, 33554432usize),
                (102usize, 33554432usize),
                (104usize, 33554432usize),
                (118usize, 33554432usize),
                (120usize, 33554432usize),
                (175usize, 33554432usize),
                (176usize, 67108864usize),
                (177usize, 1476396101usize),
                (178usize, 939526281usize),
                (195usize, 536870912usize),
                (196usize, 268435454usize),
                (202usize, 33554432usize),
                (203usize, 33554432usize),
                (204usize, 67108864usize),
                (205usize, 1476396101usize),
                (206usize, 939526281usize),
                (263usize, 1073741816usize),
                (266usize, 33554432usize),
                (357usize, 33554432usize),
                (358usize, 67108864usize),
                (359usize, 1476396101usize),
                (360usize, 939526281usize),
                (375usize, 536870912usize),
                (376usize, 268435454usize),
                (382usize, 33554432usize),
                (383usize, 33554432usize),
                (384usize, 67108864usize),
                (385usize, 1476396101usize),
                (386usize, 939526281usize),
                (388usize, 1979711489usize),
                (514usize, 268435454usize),
                (512usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (518usize, 268435454usize),
                (351usize, 268435454usize),
                (517usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 14usize),
                (0usize, 2usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 17usize] = [
                (519usize, 268435454usize),
                (51usize, 33554432usize),
                (231usize, 33554432usize),
                (232usize, 536870908usize),
                (233usize, 1476396101usize),
                (256usize, 33554432usize),
                (257usize, 536870908usize),
                (259usize, 1476396101usize),
                (321usize, 33554432usize),
                (322usize, 536870908usize),
                (323usize, 1476396101usize),
                (346usize, 33554432usize),
                (347usize, 536870908usize),
                (349usize, 1476396101usize),
                (351usize, 1979711489usize),
                (23usize, 33554432usize),
                (517usize, 1979711489usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (522usize, 268435454usize),
                (520usize, 268435454usize),
                (518usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 24usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 26usize] = [
                (523usize, 268435454usize),
                (24usize, 33554432usize),
                (40usize, 33554432usize),
                (105usize, 33554432usize),
                (107usize, 33554432usize),
                (121usize, 33554432usize),
                (123usize, 33554432usize),
                (221usize, 1476396101usize),
                (222usize, 939526281usize),
                (243usize, 33554432usize),
                (246usize, 536870912usize),
                (247usize, 268435454usize),
                (249usize, 1476396101usize),
                (250usize, 939526281usize),
                (310usize, 33554432usize),
                (311usize, 1073741816usize),
                (401usize, 1476396101usize),
                (402usize, 939526281usize),
                (421usize, 33554432usize),
                (424usize, 536870912usize),
                (425usize, 268435454usize),
                (427usize, 1476396101usize),
                (428usize, 939526281usize),
                (431usize, 1979711489usize),
                (521usize, 268435454usize),
                (519usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (525usize, 268435454usize),
                (352usize, 268435454usize),
                (524usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 18usize),
                (0usize, 2usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 21usize] = [
                (526usize, 268435454usize),
                (52usize, 33554432usize),
                (228usize, 33554432usize),
                (229usize, 536870908usize),
                (233usize, 33554432usize),
                (234usize, 1476396101usize),
                (255usize, 536870908usize),
                (258usize, 33554432usize),
                (259usize, 33554432usize),
                (260usize, 1476396101usize),
                (319usize, 33554432usize),
                (320usize, 536870908usize),
                (323usize, 33554432usize),
                (324usize, 1476396101usize),
                (345usize, 536870908usize),
                (348usize, 33554432usize),
                (349usize, 33554432usize),
                (350usize, 1476396101usize),
                (352usize, 1979711489usize),
                (25usize, 33554432usize),
                (524usize, 1979711489usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (529usize, 268435454usize),
                (527usize, 268435454usize),
                (525usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 32usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 34usize] = [
                (530usize, 268435454usize),
                (26usize, 33554432usize),
                (42usize, 33554432usize),
                (106usize, 33554432usize),
                (108usize, 33554432usize),
                (122usize, 33554432usize),
                (124usize, 33554432usize),
                (221usize, 33554432usize),
                (222usize, 67108864usize),
                (223usize, 1476396101usize),
                (224usize, 939526281usize),
                (241usize, 536870912usize),
                (242usize, 268435454usize),
                (248usize, 33554432usize),
                (249usize, 33554432usize),
                (250usize, 67108864usize),
                (251usize, 1476396101usize),
                (252usize, 939526281usize),
                (309usize, 1073741816usize),
                (312usize, 33554432usize),
                (401usize, 33554432usize),
                (402usize, 67108864usize),
                (403usize, 1476396101usize),
                (404usize, 939526281usize),
                (419usize, 536870912usize),
                (420usize, 268435454usize),
                (426usize, 33554432usize),
                (427usize, 33554432usize),
                (428usize, 67108864usize),
                (429usize, 1476396101usize),
                (430usize, 939526281usize),
                (432usize, 1979711489usize),
                (528usize, 268435454usize),
                (526usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (532usize, 268435454usize),
                (395usize, 268435454usize),
                (531usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 14usize),
                (0usize, 2usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 17usize] = [
                (533usize, 268435454usize),
                (53usize, 33554432usize),
                (277usize, 33554432usize),
                (278usize, 536870908usize),
                (279usize, 1476396101usize),
                (302usize, 33554432usize),
                (303usize, 536870908usize),
                (305usize, 1476396101usize),
                (365usize, 33554432usize),
                (366usize, 536870908usize),
                (367usize, 1476396101usize),
                (390usize, 33554432usize),
                (391usize, 536870908usize),
                (393usize, 1476396101usize),
                (395usize, 1979711489usize),
                (27usize, 33554432usize),
                (531usize, 1979711489usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (536usize, 268435454usize),
                (534usize, 268435454usize),
                (532usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 24usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 26usize] = [
                (537usize, 268435454usize),
                (28usize, 33554432usize),
                (44usize, 33554432usize),
                (109usize, 33554432usize),
                (111usize, 33554432usize),
                (125usize, 33554432usize),
                (127usize, 33554432usize),
                (172usize, 33554432usize),
                (173usize, 1073741816usize),
                (267usize, 1476396101usize),
                (268usize, 939526281usize),
                (289usize, 33554432usize),
                (292usize, 536870912usize),
                (293usize, 268435454usize),
                (295usize, 1476396101usize),
                (296usize, 939526281usize),
                (445usize, 1476396101usize),
                (446usize, 939526281usize),
                (465usize, 33554432usize),
                (468usize, 536870912usize),
                (469usize, 268435454usize),
                (471usize, 1476396101usize),
                (472usize, 939526281usize),
                (475usize, 1979711489usize),
                (535usize, 268435454usize),
                (533usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (539usize, 268435454usize),
                (396usize, 268435454usize),
                (538usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 18usize),
                (0usize, 2usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 21usize] = [
                (540usize, 268435454usize),
                (54usize, 33554432usize),
                (274usize, 33554432usize),
                (275usize, 536870908usize),
                (279usize, 33554432usize),
                (280usize, 1476396101usize),
                (301usize, 536870908usize),
                (304usize, 33554432usize),
                (305usize, 33554432usize),
                (306usize, 1476396101usize),
                (363usize, 33554432usize),
                (364usize, 536870908usize),
                (367usize, 33554432usize),
                (368usize, 1476396101usize),
                (389usize, 536870908usize),
                (392usize, 33554432usize),
                (393usize, 33554432usize),
                (394usize, 1476396101usize),
                (396usize, 1979711489usize),
                (29usize, 33554432usize),
                (538usize, 1979711489usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (543usize, 268435454usize),
                (541usize, 268435454usize),
                (539usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 32usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 34usize] = [
                (544usize, 268435454usize),
                (30usize, 33554432usize),
                (46usize, 33554432usize),
                (110usize, 33554432usize),
                (112usize, 33554432usize),
                (126usize, 33554432usize),
                (128usize, 33554432usize),
                (171usize, 1073741816usize),
                (174usize, 33554432usize),
                (267usize, 33554432usize),
                (268usize, 67108864usize),
                (269usize, 1476396101usize),
                (270usize, 939526281usize),
                (287usize, 536870912usize),
                (288usize, 268435454usize),
                (294usize, 33554432usize),
                (295usize, 33554432usize),
                (296usize, 67108864usize),
                (297usize, 1476396101usize),
                (298usize, 939526281usize),
                (445usize, 33554432usize),
                (446usize, 67108864usize),
                (447usize, 1476396101usize),
                (448usize, 939526281usize),
                (463usize, 536870912usize),
                (464usize, 268435454usize),
                (470usize, 33554432usize),
                (471usize, 33554432usize),
                (472usize, 67108864usize),
                (473usize, 1476396101usize),
                (474usize, 939526281usize),
                (476usize, 1979711489usize),
                (542usize, 268435454usize),
                (540usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (546usize, 268435454usize),
                (545usize, 268435454usize),
                (486usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 2usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (547usize, 268435454usize),
                (31usize, 8388608usize),
                (545usize, 2004877313usize),
                (487usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (550usize, 268435454usize),
                (548usize, 268435454usize),
                (390usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 2usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (551usize, 268435454usize),
                (547usize, 536870908usize),
                (549usize, 268435454usize),
                (391usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (553usize, 268435454usize),
                (552usize, 268435454usize),
                (488usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 2usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (554usize, 268435454usize),
                (33usize, 8388608usize),
                (552usize, 2004877313usize),
                (485usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (557usize, 268435454usize),
                (555usize, 268435454usize),
                (392usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 2usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (558usize, 268435454usize),
                (554usize, 536870908usize),
                (556usize, 268435454usize),
                (389usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (560usize, 268435454usize),
                (559usize, 268435454usize),
                (354usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 2usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (561usize, 268435454usize),
                (35usize, 8388608usize),
                (559usize, 2004877313usize),
                (355usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (564usize, 268435454usize),
                (562usize, 268435454usize),
                (434usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 2usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (565usize, 268435454usize),
                (561usize, 536870908usize),
                (563usize, 268435454usize),
                (435usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (567usize, 268435454usize),
                (566usize, 268435454usize),
                (356usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 2usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (568usize, 268435454usize),
                (37usize, 8388608usize),
                (566usize, 2004877313usize),
                (353usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (571usize, 268435454usize),
                (569usize, 268435454usize),
                (436usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 2usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (572usize, 268435454usize),
                (568usize, 536870908usize),
                (570usize, 268435454usize),
                (433usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (574usize, 268435454usize),
                (573usize, 268435454usize),
                (398usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 2usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (575usize, 268435454usize),
                (39usize, 8388608usize),
                (573usize, 2004877313usize),
                (399usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (578usize, 268435454usize),
                (576usize, 268435454usize),
                (478usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 2usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (579usize, 268435454usize),
                (575usize, 536870908usize),
                (577usize, 268435454usize),
                (479usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (581usize, 268435454usize),
                (580usize, 268435454usize),
                (400usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 2usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (582usize, 268435454usize),
                (41usize, 8388608usize),
                (580usize, 2004877313usize),
                (397usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (585usize, 268435454usize),
                (583usize, 268435454usize),
                (480usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 2usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (586usize, 268435454usize),
                (582usize, 536870908usize),
                (584usize, 268435454usize),
                (477usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (588usize, 268435454usize),
                (587usize, 268435454usize),
                (442usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 2usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (589usize, 268435454usize),
                (43usize, 8388608usize),
                (587usize, 2004877313usize),
                (443usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (592usize, 268435454usize),
                (590usize, 268435454usize),
                (346usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 2usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (593usize, 268435454usize),
                (589usize, 536870908usize),
                (591usize, 268435454usize),
                (347usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1342177238usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (595usize, 268435454usize),
                (594usize, 268435454usize),
                (444usize, 268435454usize),
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
            const A_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741784usize, 0usize),
                (0usize, 1usize),
                (0usize, 2usize),
                (0usize, 1usize),
            ];
            const A_VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (596usize, 268435454usize),
                (45usize, 8388608usize),
                (594usize, 2004877313usize),
                (441usize, 268435454usize),
            ];
            let mut a_val =
                eval_vector_lookup(evals, lookup_alpha, &A_VAL_COLS, &A_VAL_VL_TERMS, j);
            const B_VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 1usize),
            ];
            const B_VAL_VL_TERMS: [(usize, usize); 3usize] = [
                (599usize, 268435454usize),
                (597usize, 268435454usize),
                (348usize, 268435454usize),
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
            const VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 2usize),
                (0usize, 1usize),
            ];
            const VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (600usize, 268435454usize),
                (596usize, 536870908usize),
                (598usize, 268435454usize),
                (345usize, 268435454usize),
            ];
            let mut val = eval_vector_lookup(evals, lookup_alpha, &VAL_COLS, &VAL_VL_TERMS, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(868usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(868usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(868usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_LN: [(usize, usize); 14usize] = [
                (0usize, 268435454usize),
                (1usize, 536870908usize),
                (2usize, 1073741816usize),
                (3usize, 134217711usize),
                (4usize, 268435422usize),
                (5usize, 536870844usize),
                (6usize, 1073741688usize),
                (7usize, 134217455usize),
                (8usize, 268434910usize),
                (9usize, 536869820usize),
                (10usize, 1073739640usize),
                (11usize, 134213359usize),
                (12usize, 268426718usize),
                (865usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(9usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(12usize, 268435454usize), (13usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QI: [(usize, usize); 1usize] = [(3usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(3usize, 268435454usize), (14usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QI: [(usize, usize); 1usize] = [(652usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 268309694usize),
                (15usize, 1744830467usize),
                (652usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(15usize, 268435454usize), (700usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(16usize, 1744830467usize), (700usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QI: [(usize, usize); 1usize] = [(653usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 671030187usize),
                (17usize, 1744830467usize),
                (653usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(17usize, 268435454usize), (701usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(18usize, 1744830467usize), (701usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QI: [(usize, usize); 1usize] = [(658usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1878952882usize),
                (19usize, 1744830467usize),
                (658usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(19usize, 268435454usize), (706usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(20usize, 1744830467usize), (706usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QI: [(usize, usize); 1usize] = [(659usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1342074934usize),
                (21usize, 1744830467usize),
                (659usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(21usize, 268435454usize), (707usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(22usize, 1744830467usize), (707usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QI: [(usize, usize); 1usize] = [(664usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1207826599usize),
                (23usize, 1744830467usize),
                (664usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(23usize, 268435454usize), (712usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(24usize, 1744830467usize), (712usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QI: [(usize, usize); 1usize] = [(665usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1342144278usize),
                (25usize, 1744830467usize),
                (665usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(25usize, 268435454usize), (713usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(26usize, 1744830467usize), (713usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QI: [(usize, usize); 1usize] = [(670usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 805172442usize),
                (27usize, 1744830467usize),
                (670usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(27usize, 268435454usize), (718usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(28usize, 1744830467usize), (718usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QI: [(usize, usize); 1usize] = [(671usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1073651544usize),
                (29usize, 1744830467usize),
                (671usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(29usize, 268435454usize), (719usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(30usize, 1744830467usize), (719usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QI: [(usize, usize); 1usize] = [(676usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1744785411usize),
                (31usize, 1744830467usize),
                (676usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(31usize, 268435454usize), (724usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(32usize, 1744830467usize), (724usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QI: [(usize, usize); 1usize] = [(677usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1342133014usize),
                (33usize, 1744830467usize),
                (677usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(33usize, 268435454usize), (725usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(34usize, 1744830467usize), (725usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QI: [(usize, usize); 1usize] = [(682usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1073684728usize),
                (35usize, 1744830467usize),
                (682usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(35usize, 268435454usize), (730usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(36usize, 1744830467usize), (730usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QI: [(usize, usize); 1usize] = [(683usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 671003979usize),
                (37usize, 1744830467usize),
                (683usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(37usize, 268435454usize), (731usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(38usize, 1744830467usize), (731usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QI: [(usize, usize); 1usize] = [(688usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1476276133usize),
                (39usize, 1744830467usize),
                (688usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(39usize, 268435454usize), (736usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(40usize, 1744830467usize), (736usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QI: [(usize, usize); 1usize] = [(689usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1207942343usize),
                (41usize, 1744830467usize),
                (689usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(41usize, 268435454usize), (737usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(42usize, 1744830467usize), (737usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QI: [(usize, usize); 1usize] = [(694usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1342065270usize),
                (43usize, 1744830467usize),
                (694usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(43usize, 268435454usize), (742usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(44usize, 1744830467usize), (742usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QI: [(usize, usize); 1usize] = [(695usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 2013215745usize),
                (45usize, 1744830467usize),
                (695usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(45usize, 268435454usize), (743usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(46usize, 1744830467usize), (743usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QI: [(usize, usize); 1usize] = [(748usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 805180538usize),
                (47usize, 1744830467usize),
                (748usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(749usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 671030731usize),
                (48usize, 1744830467usize),
                (749usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(754usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1878952882usize),
                (49usize, 1744830467usize),
                (754usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(755usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1342074934usize),
                (50usize, 1744830467usize),
                (755usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(760usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1207826599usize),
                (51usize, 1744830467usize),
                (760usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(761usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1342144278usize),
                (52usize, 1744830467usize),
                (761usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(766usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 805172442usize),
                (53usize, 1744830467usize),
                (766usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(767usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1073651544usize),
                (54usize, 1744830467usize),
                (767usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(778usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1073684728usize),
                (55usize, 1744830467usize),
                (778usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(779usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 671003979usize),
                (56usize, 1744830467usize),
                (779usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(790usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1342065270usize),
                (57usize, 1744830467usize),
                (790usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(791usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 2013215745usize),
                (58usize, 1744830467usize),
                (791usize, 268435454usize),
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
                [(2usize, 1usize), (3usize, 1usize), (14usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (3usize, 671043723usize),
                (772usize, 1744830467usize),
                (772usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(59usize, 1744830467usize), (772usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (3usize, 1usize), (14usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (3usize, 1342133014usize),
                (773usize, 1744830467usize),
                (773usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(60usize, 1744830467usize), (773usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (3usize, 1usize), (14usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (3usize, 536849980usize),
                (784usize, 1744830467usize),
                (784usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(61usize, 1744830467usize), (784usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (3usize, 1usize), (14usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (3usize, 805183770usize),
                (785usize, 1744830467usize),
                (785usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(62usize, 1744830467usize), (785usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QI: [(usize, usize); 1usize] = [(2usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(63usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QI: [(usize, usize); 1usize] = [(2usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(2usize, 268435454usize), (64usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (800usize, 1744830467usize),
                (800usize, 268435454usize),
                (652usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(65usize, 1744830467usize), (800usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (801usize, 1744830467usize),
                (801usize, 268435454usize),
                (653usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(66usize, 1744830467usize), (801usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (804usize, 1744830467usize),
                (804usize, 268435454usize),
                (658usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(67usize, 1744830467usize), (804usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (805usize, 1744830467usize),
                (805usize, 268435454usize),
                (659usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(68usize, 1744830467usize), (805usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (808usize, 1744830467usize),
                (808usize, 268435454usize),
                (664usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(69usize, 1744830467usize), (808usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (809usize, 1744830467usize),
                (809usize, 268435454usize),
                (665usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(70usize, 1744830467usize), (809usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (812usize, 1744830467usize),
                (812usize, 268435454usize),
                (670usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(71usize, 1744830467usize), (812usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (813usize, 1744830467usize),
                (813usize, 268435454usize),
                (671usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(72usize, 1744830467usize), (813usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (816usize, 1744830467usize),
                (816usize, 268435454usize),
                (676usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(73usize, 1744830467usize), (816usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (817usize, 1744830467usize),
                (817usize, 268435454usize),
                (677usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(74usize, 1744830467usize), (817usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (820usize, 1744830467usize),
                (820usize, 268435454usize),
                (682usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(75usize, 1744830467usize), (820usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (821usize, 1744830467usize),
                (821usize, 268435454usize),
                (683usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(76usize, 1744830467usize), (821usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (824usize, 1744830467usize),
                (824usize, 268435454usize),
                (688usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(77usize, 1744830467usize), (824usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (825usize, 1744830467usize),
                (825usize, 268435454usize),
                (689usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(78usize, 1744830467usize), (825usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (828usize, 1744830467usize),
                (828usize, 268435454usize),
                (694usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(79usize, 1744830467usize), (828usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (829usize, 1744830467usize),
                (829usize, 268435454usize),
                (695usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(80usize, 1744830467usize), (829usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (832usize, 1744830467usize),
                (652usize, 268435454usize),
                (800usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(81usize, 1744830467usize), (832usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (833usize, 1744830467usize),
                (653usize, 268435454usize),
                (801usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(82usize, 1744830467usize), (833usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (836usize, 1744830467usize),
                (658usize, 268435454usize),
                (804usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(83usize, 1744830467usize), (836usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (837usize, 1744830467usize),
                (659usize, 268435454usize),
                (805usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(84usize, 1744830467usize), (837usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (840usize, 1744830467usize),
                (664usize, 268435454usize),
                (808usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(85usize, 1744830467usize), (840usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (841usize, 1744830467usize),
                (665usize, 268435454usize),
                (809usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(86usize, 1744830467usize), (841usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (844usize, 1744830467usize),
                (670usize, 268435454usize),
                (812usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(87usize, 1744830467usize), (844usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (845usize, 1744830467usize),
                (671usize, 268435454usize),
                (813usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(88usize, 1744830467usize), (845usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (848usize, 1744830467usize),
                (676usize, 268435454usize),
                (816usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(89usize, 1744830467usize), (848usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (849usize, 1744830467usize),
                (677usize, 268435454usize),
                (817usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(90usize, 1744830467usize), (849usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (852usize, 1744830467usize),
                (682usize, 268435454usize),
                (820usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(91usize, 1744830467usize), (852usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (853usize, 1744830467usize),
                (683usize, 268435454usize),
                (821usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(92usize, 1744830467usize), (853usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (856usize, 1744830467usize),
                (688usize, 268435454usize),
                (824usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(93usize, 1744830467usize), (856usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (857usize, 1744830467usize),
                (689usize, 268435454usize),
                (825usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(94usize, 1744830467usize), (857usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (860usize, 1744830467usize),
                (694usize, 268435454usize),
                (828usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(95usize, 1744830467usize), (860usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (861usize, 1744830467usize),
                (695usize, 268435454usize),
                (829usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(96usize, 1744830467usize), (861usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (65usize, 268435454usize),
                (93usize, 268435454usize),
                (87usize, 268435454usize),
                (79usize, 268435454usize),
                (83usize, 268435454usize),
                (69usize, 268435454usize),
                (89usize, 268435454usize),
                (91usize, 268435454usize),
                (77usize, 268435454usize),
                (85usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(97usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (66usize, 268435454usize),
                (94usize, 268435454usize),
                (88usize, 268435454usize),
                (80usize, 268435454usize),
                (84usize, 268435454usize),
                (70usize, 268435454usize),
                (90usize, 268435454usize),
                (92usize, 268435454usize),
                (78usize, 268435454usize),
                (86usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(98usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (67usize, 268435454usize),
                (85usize, 268435454usize),
                (81usize, 268435454usize),
                (83usize, 268435454usize),
                (65usize, 268435454usize),
                (89usize, 268435454usize),
                (75usize, 268435454usize),
                (87usize, 268435454usize),
                (95usize, 268435454usize),
                (69usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(99usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (68usize, 268435454usize),
                (86usize, 268435454usize),
                (82usize, 268435454usize),
                (84usize, 268435454usize),
                (66usize, 268435454usize),
                (90usize, 268435454usize),
                (76usize, 268435454usize),
                (88usize, 268435454usize),
                (96usize, 268435454usize),
                (70usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(100usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (69usize, 268435454usize),
                (73usize, 268435454usize),
                (89usize, 268435454usize),
                (71usize, 268435454usize),
                (75usize, 268435454usize),
                (77usize, 268435454usize),
                (67usize, 268435454usize),
                (79usize, 268435454usize),
                (93usize, 268435454usize),
                (81usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(101usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (70usize, 268435454usize),
                (74usize, 268435454usize),
                (90usize, 268435454usize),
                (72usize, 268435454usize),
                (76usize, 268435454usize),
                (78usize, 268435454usize),
                (68usize, 268435454usize),
                (80usize, 268435454usize),
                (94usize, 268435454usize),
                (82usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(102usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (71usize, 268435454usize),
                (81usize, 268435454usize),
                (65usize, 268435454usize),
                (67usize, 268435454usize),
                (79usize, 268435454usize),
                (85usize, 268435454usize),
                (95usize, 268435454usize),
                (93usize, 268435454usize),
                (83usize, 268435454usize),
                (73usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(103usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (72usize, 268435454usize),
                (82usize, 268435454usize),
                (66usize, 268435454usize),
                (68usize, 268435454usize),
                (80usize, 268435454usize),
                (86usize, 268435454usize),
                (96usize, 268435454usize),
                (94usize, 268435454usize),
                (84usize, 268435454usize),
                (74usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (73usize, 268435454usize),
                (83usize, 268435454usize),
                (75usize, 268435454usize),
                (91usize, 268435454usize),
                (69usize, 268435454usize),
                (65usize, 268435454usize),
                (93usize, 268435454usize),
                (89usize, 268435454usize),
                (87usize, 268435454usize),
                (79usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(105usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (74usize, 268435454usize),
                (84usize, 268435454usize),
                (76usize, 268435454usize),
                (92usize, 268435454usize),
                (70usize, 268435454usize),
                (66usize, 268435454usize),
                (94usize, 268435454usize),
                (90usize, 268435454usize),
                (88usize, 268435454usize),
                (80usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(106usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (75usize, 268435454usize),
                (95usize, 268435454usize),
                (69usize, 268435454usize),
                (89usize, 268435454usize),
                (73usize, 268435454usize),
                (87usize, 268435454usize),
                (91usize, 268435454usize),
                (67usize, 268435454usize),
                (71usize, 268435454usize),
                (77usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(107usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (76usize, 268435454usize),
                (96usize, 268435454usize),
                (70usize, 268435454usize),
                (90usize, 268435454usize),
                (74usize, 268435454usize),
                (88usize, 268435454usize),
                (92usize, 268435454usize),
                (68usize, 268435454usize),
                (72usize, 268435454usize),
                (78usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(108usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (77usize, 268435454usize),
                (91usize, 268435454usize),
                (95usize, 268435454usize),
                (87usize, 268435454usize),
                (85usize, 268435454usize),
                (81usize, 268435454usize),
                (73usize, 268435454usize),
                (71usize, 268435454usize),
                (65usize, 268435454usize),
                (67usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(109usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (78usize, 268435454usize),
                (92usize, 268435454usize),
                (96usize, 268435454usize),
                (88usize, 268435454usize),
                (86usize, 268435454usize),
                (82usize, 268435454usize),
                (74usize, 268435454usize),
                (72usize, 268435454usize),
                (66usize, 268435454usize),
                (68usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(110usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (79usize, 268435454usize),
                (77usize, 268435454usize),
                (91usize, 268435454usize),
                (93usize, 268435454usize),
                (95usize, 268435454usize),
                (71usize, 268435454usize),
                (85usize, 268435454usize),
                (83usize, 268435454usize),
                (81usize, 268435454usize),
                (75usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(111usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (80usize, 268435454usize),
                (78usize, 268435454usize),
                (92usize, 268435454usize),
                (94usize, 268435454usize),
                (96usize, 268435454usize),
                (72usize, 268435454usize),
                (86usize, 268435454usize),
                (84usize, 268435454usize),
                (82usize, 268435454usize),
                (76usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(112usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (81usize, 268435454usize),
                (67usize, 268435454usize),
                (85usize, 268435454usize),
                (69usize, 268435454usize),
                (93usize, 268435454usize),
                (73usize, 268435454usize),
                (65usize, 268435454usize),
                (75usize, 268435454usize),
                (89usize, 268435454usize),
                (95usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(113usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (82usize, 268435454usize),
                (68usize, 268435454usize),
                (86usize, 268435454usize),
                (70usize, 268435454usize),
                (94usize, 268435454usize),
                (74usize, 268435454usize),
                (66usize, 268435454usize),
                (76usize, 268435454usize),
                (90usize, 268435454usize),
                (96usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(114usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (83usize, 268435454usize),
                (89usize, 268435454usize),
                (93usize, 268435454usize),
                (77usize, 268435454usize),
                (67usize, 268435454usize),
                (91usize, 268435454usize),
                (79usize, 268435454usize),
                (65usize, 268435454usize),
                (69usize, 268435454usize),
                (87usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(115usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (84usize, 268435454usize),
                (90usize, 268435454usize),
                (94usize, 268435454usize),
                (78usize, 268435454usize),
                (68usize, 268435454usize),
                (92usize, 268435454usize),
                (80usize, 268435454usize),
                (66usize, 268435454usize),
                (70usize, 268435454usize),
                (88usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(116usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (85usize, 268435454usize),
                (65usize, 268435454usize),
                (71usize, 268435454usize),
                (75usize, 268435454usize),
                (87usize, 268435454usize),
                (79usize, 268435454usize),
                (77usize, 268435454usize),
                (95usize, 268435454usize),
                (91usize, 268435454usize),
                (83usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(117usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (86usize, 268435454usize),
                (66usize, 268435454usize),
                (72usize, 268435454usize),
                (76usize, 268435454usize),
                (88usize, 268435454usize),
                (80usize, 268435454usize),
                (78usize, 268435454usize),
                (96usize, 268435454usize),
                (92usize, 268435454usize),
                (84usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(118usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (87usize, 268435454usize),
                (69usize, 268435454usize),
                (77usize, 268435454usize),
                (85usize, 268435454usize),
                (89usize, 268435454usize),
                (75usize, 268435454usize),
                (71usize, 268435454usize),
                (73usize, 268435454usize),
                (79usize, 268435454usize),
                (93usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(119usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (88usize, 268435454usize),
                (70usize, 268435454usize),
                (78usize, 268435454usize),
                (86usize, 268435454usize),
                (90usize, 268435454usize),
                (76usize, 268435454usize),
                (72usize, 268435454usize),
                (74usize, 268435454usize),
                (80usize, 268435454usize),
                (94usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(120usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (89usize, 268435454usize),
                (87usize, 268435454usize),
                (79usize, 268435454usize),
                (73usize, 268435454usize),
                (77usize, 268435454usize),
                (95usize, 268435454usize),
                (83usize, 268435454usize),
                (81usize, 268435454usize),
                (67usize, 268435454usize),
                (71usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(121usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (90usize, 268435454usize),
                (88usize, 268435454usize),
                (80usize, 268435454usize),
                (74usize, 268435454usize),
                (78usize, 268435454usize),
                (96usize, 268435454usize),
                (84usize, 268435454usize),
                (82usize, 268435454usize),
                (68usize, 268435454usize),
                (72usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(122usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (91usize, 268435454usize),
                (79usize, 268435454usize),
                (67usize, 268435454usize),
                (65usize, 268435454usize),
                (81usize, 268435454usize),
                (93usize, 268435454usize),
                (69usize, 268435454usize),
                (77usize, 268435454usize),
                (73usize, 268435454usize),
                (89usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(123usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (92usize, 268435454usize),
                (80usize, 268435454usize),
                (68usize, 268435454usize),
                (66usize, 268435454usize),
                (82usize, 268435454usize),
                (94usize, 268435454usize),
                (70usize, 268435454usize),
                (78usize, 268435454usize),
                (74usize, 268435454usize),
                (90usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(124usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (93usize, 268435454usize),
                (75usize, 268435454usize),
                (83usize, 268435454usize),
                (95usize, 268435454usize),
                (71usize, 268435454usize),
                (67usize, 268435454usize),
                (81usize, 268435454usize),
                (69usize, 268435454usize),
                (85usize, 268435454usize),
                (91usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(125usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (94usize, 268435454usize),
                (76usize, 268435454usize),
                (84usize, 268435454usize),
                (96usize, 268435454usize),
                (72usize, 268435454usize),
                (68usize, 268435454usize),
                (82usize, 268435454usize),
                (70usize, 268435454usize),
                (86usize, 268435454usize),
                (92usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(126usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (95usize, 268435454usize),
                (71usize, 268435454usize),
                (73usize, 268435454usize),
                (81usize, 268435454usize),
                (91usize, 268435454usize),
                (83usize, 268435454usize),
                (87usize, 268435454usize),
                (85usize, 268435454usize),
                (75usize, 268435454usize),
                (65usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(127usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 10usize] = [
                (3usize, 1usize),
                (4usize, 1usize),
                (5usize, 1usize),
                (6usize, 1usize),
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
                (12usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (96usize, 268435454usize),
                (72usize, 268435454usize),
                (74usize, 268435454usize),
                (82usize, 268435454usize),
                (92usize, 268435454usize),
                (84usize, 268435454usize),
                (88usize, 268435454usize),
                (86usize, 268435454usize),
                (76usize, 268435454usize),
                (66usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(128usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_LN: [(usize, usize); 1usize] = [(866usize, 268435454usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_LN: [(usize, usize); 13usize] = [
                (0usize, 268435454usize),
                (1usize, 536870908usize),
                (2usize, 1073741816usize),
                (3usize, 268435422usize),
                (4usize, 536870844usize),
                (5usize, 1073741688usize),
                (6usize, 134217455usize),
                (7usize, 268434910usize),
                (8usize, 536869820usize),
                (9usize, 1073739640usize),
                (10usize, 134213359usize),
                (11usize, 268426718usize),
                (867usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 23usize] = [
                (16usize, 268435454usize),
                (32usize, 268435454usize),
                (97usize, 268435454usize),
                (99usize, 268435454usize),
                (113usize, 268435454usize),
                (115usize, 268435454usize),
                (129usize, 1744970275usize),
                (130usize, 1476674629usize),
                (151usize, 268435454usize),
                (154usize, 268435422usize),
                (155usize, 134217455usize),
                (157usize, 1744970275usize),
                (158usize, 1476674629usize),
                (218usize, 268435454usize),
                (219usize, 536869820usize),
                (313usize, 1744970275usize),
                (314usize, 1476674629usize),
                (333usize, 268435454usize),
                (336usize, 268435422usize),
                (337usize, 134217455usize),
                (339usize, 1744970275usize),
                (340usize, 1476674629usize),
                (702usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 31usize] = [
                (18usize, 268435454usize),
                (34usize, 268435454usize),
                (98usize, 268435454usize),
                (100usize, 268435454usize),
                (114usize, 268435454usize),
                (116usize, 268435454usize),
                (129usize, 268435454usize),
                (130usize, 536870908usize),
                (131usize, 1744970275usize),
                (132usize, 1476674629usize),
                (149usize, 268435422usize),
                (150usize, 134217455usize),
                (156usize, 268435454usize),
                (157usize, 268435454usize),
                (158usize, 536870908usize),
                (159usize, 1744970275usize),
                (160usize, 1476674629usize),
                (217usize, 536869820usize),
                (220usize, 268435454usize),
                (313usize, 268435454usize),
                (314usize, 536870908usize),
                (315usize, 1744970275usize),
                (316usize, 1476674629usize),
                (331usize, 268435422usize),
                (332usize, 134217455usize),
                (338usize, 268435454usize),
                (339usize, 268435454usize),
                (340usize, 536870908usize),
                (341usize, 1744970275usize),
                (342usize, 1476674629usize),
                (703usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 23usize] = [
                (20usize, 268435454usize),
                (36usize, 268435454usize),
                (101usize, 268435454usize),
                (103usize, 268435454usize),
                (117usize, 268435454usize),
                (119usize, 268435454usize),
                (175usize, 1744970275usize),
                (176usize, 1476674629usize),
                (197usize, 268435454usize),
                (200usize, 268435422usize),
                (201usize, 134217455usize),
                (203usize, 1744970275usize),
                (204usize, 1476674629usize),
                (264usize, 268435454usize),
                (265usize, 536869820usize),
                (357usize, 1744970275usize),
                (358usize, 1476674629usize),
                (377usize, 268435454usize),
                (380usize, 268435422usize),
                (381usize, 134217455usize),
                (383usize, 1744970275usize),
                (384usize, 1476674629usize),
                (708usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 31usize] = [
                (22usize, 268435454usize),
                (38usize, 268435454usize),
                (102usize, 268435454usize),
                (104usize, 268435454usize),
                (118usize, 268435454usize),
                (120usize, 268435454usize),
                (175usize, 268435454usize),
                (176usize, 536870908usize),
                (177usize, 1744970275usize),
                (178usize, 1476674629usize),
                (195usize, 268435422usize),
                (196usize, 134217455usize),
                (202usize, 268435454usize),
                (203usize, 268435454usize),
                (204usize, 536870908usize),
                (205usize, 1744970275usize),
                (206usize, 1476674629usize),
                (263usize, 536869820usize),
                (266usize, 268435454usize),
                (357usize, 268435454usize),
                (358usize, 536870908usize),
                (359usize, 1744970275usize),
                (360usize, 1476674629usize),
                (375usize, 268435422usize),
                (376usize, 134217455usize),
                (382usize, 268435454usize),
                (383usize, 268435454usize),
                (384usize, 536870908usize),
                (385usize, 1744970275usize),
                (386usize, 1476674629usize),
                (709usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 23usize] = [
                (24usize, 268435454usize),
                (40usize, 268435454usize),
                (105usize, 268435454usize),
                (107usize, 268435454usize),
                (121usize, 268435454usize),
                (123usize, 268435454usize),
                (221usize, 1744970275usize),
                (222usize, 1476674629usize),
                (243usize, 268435454usize),
                (246usize, 268435422usize),
                (247usize, 134217455usize),
                (249usize, 1744970275usize),
                (250usize, 1476674629usize),
                (310usize, 268435454usize),
                (311usize, 536869820usize),
                (401usize, 1744970275usize),
                (402usize, 1476674629usize),
                (421usize, 268435454usize),
                (424usize, 268435422usize),
                (425usize, 134217455usize),
                (427usize, 1744970275usize),
                (428usize, 1476674629usize),
                (714usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 31usize] = [
                (26usize, 268435454usize),
                (42usize, 268435454usize),
                (106usize, 268435454usize),
                (108usize, 268435454usize),
                (122usize, 268435454usize),
                (124usize, 268435454usize),
                (221usize, 268435454usize),
                (222usize, 536870908usize),
                (223usize, 1744970275usize),
                (224usize, 1476674629usize),
                (241usize, 268435422usize),
                (242usize, 134217455usize),
                (248usize, 268435454usize),
                (249usize, 268435454usize),
                (250usize, 536870908usize),
                (251usize, 1744970275usize),
                (252usize, 1476674629usize),
                (309usize, 536869820usize),
                (312usize, 268435454usize),
                (401usize, 268435454usize),
                (402usize, 536870908usize),
                (403usize, 1744970275usize),
                (404usize, 1476674629usize),
                (419usize, 268435422usize),
                (420usize, 134217455usize),
                (426usize, 268435454usize),
                (427usize, 268435454usize),
                (428usize, 536870908usize),
                (429usize, 1744970275usize),
                (430usize, 1476674629usize),
                (715usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 23usize] = [
                (28usize, 268435454usize),
                (44usize, 268435454usize),
                (109usize, 268435454usize),
                (111usize, 268435454usize),
                (125usize, 268435454usize),
                (127usize, 268435454usize),
                (172usize, 268435454usize),
                (173usize, 536869820usize),
                (267usize, 1744970275usize),
                (268usize, 1476674629usize),
                (289usize, 268435454usize),
                (292usize, 268435422usize),
                (293usize, 134217455usize),
                (295usize, 1744970275usize),
                (296usize, 1476674629usize),
                (445usize, 1744970275usize),
                (446usize, 1476674629usize),
                (465usize, 268435454usize),
                (468usize, 268435422usize),
                (469usize, 134217455usize),
                (471usize, 1744970275usize),
                (472usize, 1476674629usize),
                (720usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 31usize] = [
                (30usize, 268435454usize),
                (46usize, 268435454usize),
                (110usize, 268435454usize),
                (112usize, 268435454usize),
                (126usize, 268435454usize),
                (128usize, 268435454usize),
                (171usize, 536869820usize),
                (174usize, 268435454usize),
                (267usize, 268435454usize),
                (268usize, 536870908usize),
                (269usize, 1744970275usize),
                (270usize, 1476674629usize),
                (287usize, 268435422usize),
                (288usize, 134217455usize),
                (294usize, 268435454usize),
                (295usize, 268435454usize),
                (296usize, 536870908usize),
                (297usize, 1744970275usize),
                (298usize, 1476674629usize),
                (445usize, 268435454usize),
                (446usize, 536870908usize),
                (447usize, 1744970275usize),
                (448usize, 1476674629usize),
                (463usize, 268435422usize),
                (464usize, 134217455usize),
                (470usize, 268435454usize),
                (471usize, 268435454usize),
                (472usize, 536870908usize),
                (473usize, 1744970275usize),
                (474usize, 1476674629usize),
                (721usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (486usize, 268435454usize),
                (487usize, 536869820usize),
                (726usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (485usize, 536869820usize),
                (488usize, 268435454usize),
                (727usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (354usize, 268435454usize),
                (355usize, 536869820usize),
                (732usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (353usize, 536869820usize),
                (356usize, 268435454usize),
                (733usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (398usize, 268435454usize),
                (399usize, 536869820usize),
                (738usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (397usize, 536869820usize),
                (400usize, 268435454usize),
                (739usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (442usize, 268435454usize),
                (443usize, 536869820usize),
                (744usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (441usize, 536869820usize),
                (444usize, 268435454usize),
                (745usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 14usize] = [
                (47usize, 268435454usize),
                (139usize, 268435454usize),
                (140usize, 268434910usize),
                (141usize, 1744970275usize),
                (164usize, 268435454usize),
                (165usize, 268434910usize),
                (167usize, 1744970275usize),
                (409usize, 268435454usize),
                (410usize, 268434910usize),
                (411usize, 1744970275usize),
                (434usize, 268435454usize),
                (435usize, 268434910usize),
                (437usize, 1744970275usize),
                (750usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 18usize] = [
                (48usize, 268435454usize),
                (136usize, 268435454usize),
                (137usize, 268434910usize),
                (141usize, 268435454usize),
                (142usize, 1744970275usize),
                (163usize, 268434910usize),
                (166usize, 268435454usize),
                (167usize, 268435454usize),
                (168usize, 1744970275usize),
                (407usize, 268435454usize),
                (408usize, 268434910usize),
                (411usize, 268435454usize),
                (412usize, 1744970275usize),
                (433usize, 268434910usize),
                (436usize, 268435454usize),
                (437usize, 268435454usize),
                (438usize, 1744970275usize),
                (751usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 14usize] = [
                (49usize, 268435454usize),
                (185usize, 268435454usize),
                (186usize, 268434910usize),
                (187usize, 1744970275usize),
                (210usize, 268435454usize),
                (211usize, 268434910usize),
                (213usize, 1744970275usize),
                (453usize, 268435454usize),
                (454usize, 268434910usize),
                (455usize, 1744970275usize),
                (478usize, 268435454usize),
                (479usize, 268434910usize),
                (481usize, 1744970275usize),
                (756usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 18usize] = [
                (50usize, 268435454usize),
                (182usize, 268435454usize),
                (183usize, 268434910usize),
                (187usize, 268435454usize),
                (188usize, 1744970275usize),
                (209usize, 268434910usize),
                (212usize, 268435454usize),
                (213usize, 268435454usize),
                (214usize, 1744970275usize),
                (451usize, 268435454usize),
                (452usize, 268434910usize),
                (455usize, 268435454usize),
                (456usize, 1744970275usize),
                (477usize, 268434910usize),
                (480usize, 268435454usize),
                (481usize, 268435454usize),
                (482usize, 1744970275usize),
                (757usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 14usize] = [
                (51usize, 268435454usize),
                (231usize, 268435454usize),
                (232usize, 268434910usize),
                (233usize, 1744970275usize),
                (256usize, 268435454usize),
                (257usize, 268434910usize),
                (259usize, 1744970275usize),
                (321usize, 268435454usize),
                (322usize, 268434910usize),
                (323usize, 1744970275usize),
                (346usize, 268435454usize),
                (347usize, 268434910usize),
                (349usize, 1744970275usize),
                (762usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 18usize] = [
                (52usize, 268435454usize),
                (228usize, 268435454usize),
                (229usize, 268434910usize),
                (233usize, 268435454usize),
                (234usize, 1744970275usize),
                (255usize, 268434910usize),
                (258usize, 268435454usize),
                (259usize, 268435454usize),
                (260usize, 1744970275usize),
                (319usize, 268435454usize),
                (320usize, 268434910usize),
                (323usize, 268435454usize),
                (324usize, 1744970275usize),
                (345usize, 268434910usize),
                (348usize, 268435454usize),
                (349usize, 268435454usize),
                (350usize, 1744970275usize),
                (763usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 14usize] = [
                (53usize, 268435454usize),
                (277usize, 268435454usize),
                (278usize, 268434910usize),
                (279usize, 1744970275usize),
                (302usize, 268435454usize),
                (303usize, 268434910usize),
                (305usize, 1744970275usize),
                (365usize, 268435454usize),
                (366usize, 268434910usize),
                (367usize, 1744970275usize),
                (390usize, 268435454usize),
                (391usize, 268434910usize),
                (393usize, 1744970275usize),
                (768usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 18usize] = [
                (54usize, 268435454usize),
                (274usize, 268435454usize),
                (275usize, 268434910usize),
                (279usize, 268435454usize),
                (280usize, 1744970275usize),
                (301usize, 268434910usize),
                (304usize, 268435454usize),
                (305usize, 268435454usize),
                (306usize, 1744970275usize),
                (363usize, 268435454usize),
                (364usize, 268434910usize),
                (367usize, 268435454usize),
                (368usize, 1744970275usize),
                (389usize, 268434910usize),
                (392usize, 268435454usize),
                (393usize, 268435454usize),
                (394usize, 1744970275usize),
                (769usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (390usize, 268435454usize),
                (391usize, 268434910usize),
                (774usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (389usize, 268434910usize),
                (392usize, 268435454usize),
                (775usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (434usize, 268435454usize),
                (435usize, 268434910usize),
                (780usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (433usize, 268434910usize),
                (436usize, 268435454usize),
                (781usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (478usize, 268435454usize),
                (479usize, 268434910usize),
                (786usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (477usize, 268434910usize),
                (480usize, 268435454usize),
                (787usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (346usize, 268435454usize),
                (347usize, 268434910usize),
                (792usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (345usize, 268434910usize),
                (348usize, 268435454usize),
                (793usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (343usize, 268435454usize),
                (492usize, 1744830467usize),
                (493usize, 1879048466usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (494usize, 268435454usize),
                (495usize, 134217455usize),
                (652usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(652usize, 268435454usize), (654usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (344usize, 268435454usize),
                (499usize, 1744830467usize),
                (500usize, 1879048466usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (501usize, 268435454usize),
                (502usize, 134217455usize),
                (653usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(653usize, 268435454usize), (655usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (387usize, 268435454usize),
                (506usize, 1744830467usize),
                (507usize, 1879048466usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (508usize, 268435454usize),
                (509usize, 134217455usize),
                (658usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(658usize, 268435454usize), (660usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (388usize, 268435454usize),
                (513usize, 1744830467usize),
                (514usize, 1879048466usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (515usize, 268435454usize),
                (516usize, 134217455usize),
                (659usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(659usize, 268435454usize), (661usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (431usize, 268435454usize),
                (520usize, 1744830467usize),
                (521usize, 1879048466usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (522usize, 268435454usize),
                (523usize, 134217455usize),
                (664usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(664usize, 268435454usize), (666usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (432usize, 268435454usize),
                (527usize, 1744830467usize),
                (528usize, 1879048466usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (529usize, 268435454usize),
                (530usize, 134217455usize),
                (665usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(665usize, 268435454usize), (667usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (475usize, 268435454usize),
                (534usize, 1744830467usize),
                (535usize, 1879048466usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (536usize, 268435454usize),
                (537usize, 134217455usize),
                (670usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(670usize, 268435454usize), (672usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (476usize, 268435454usize),
                (541usize, 1744830467usize),
                (542usize, 1879048466usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (543usize, 268435454usize),
                (544usize, 134217455usize),
                (671usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(671usize, 268435454usize), (673usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (546usize, 268435454usize),
                (548usize, 1744830467usize),
                (549usize, 1744831011usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (550usize, 268435454usize),
                (551usize, 268434910usize),
                (676usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(676usize, 268435454usize), (678usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (553usize, 268435454usize),
                (555usize, 1744830467usize),
                (556usize, 1744831011usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (557usize, 268435454usize),
                (558usize, 268434910usize),
                (677usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(677usize, 268435454usize), (679usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (560usize, 268435454usize),
                (562usize, 1744830467usize),
                (563usize, 1744831011usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (564usize, 268435454usize),
                (565usize, 268434910usize),
                (682usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(682usize, 268435454usize), (684usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (567usize, 268435454usize),
                (569usize, 1744830467usize),
                (570usize, 1744831011usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (571usize, 268435454usize),
                (572usize, 268434910usize),
                (683usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(683usize, 268435454usize), (685usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (574usize, 268435454usize),
                (576usize, 1744830467usize),
                (577usize, 1744831011usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (578usize, 268435454usize),
                (579usize, 268434910usize),
                (688usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(688usize, 268435454usize), (690usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (581usize, 268435454usize),
                (583usize, 1744830467usize),
                (584usize, 1744831011usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (585usize, 268435454usize),
                (586usize, 268434910usize),
                (689usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(689usize, 268435454usize), (691usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (588usize, 268435454usize),
                (590usize, 1744830467usize),
                (591usize, 1744831011usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (592usize, 268435454usize),
                (593usize, 268434910usize),
                (694usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(694usize, 268435454usize), (696usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (595usize, 268435454usize),
                (597usize, 1744830467usize),
                (598usize, 1744831011usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (599usize, 268435454usize),
                (600usize, 268434910usize),
                (695usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(695usize, 268435454usize), (697usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QO: [(usize, usize); 1usize] = [(129usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(129usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(129usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(130usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(130usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(130usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(131usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(131usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(131usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(132usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(132usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(132usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QO: [(usize, usize); 1usize] = [(157usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(157usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(157usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(158usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(158usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(158usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
            const VAL_QO: [(usize, usize); 1usize] = [(175usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(175usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(176usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(176usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(177usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(177usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(177usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(178usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(178usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(178usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(187usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(187usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(188usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(188usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(203usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(203usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(203usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(204usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(204usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(204usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(205usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(205usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(206usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(206usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(213usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(213usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(213usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(214usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(214usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(214usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(221usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(221usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(221usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(222usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(222usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(222usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(223usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(223usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(223usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(224usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(224usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(224usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(233usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(233usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(233usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(234usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(234usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(234usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(249usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(249usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(249usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(250usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(250usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(250usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(251usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(251usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(251usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(252usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(252usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(252usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(259usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(259usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(259usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(260usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(260usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(260usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(267usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(267usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(267usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(268usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(268usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(268usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(269usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(269usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(269usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(270usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(270usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(270usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(279usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(279usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(279usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(280usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(280usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(280usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(295usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(295usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(295usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(296usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(296usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(296usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(297usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(297usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(297usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(298usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(298usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(298usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(305usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(305usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(305usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(306usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(306usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(306usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(313usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(313usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(313usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(314usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(314usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(314usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(315usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(315usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(315usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(316usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(316usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(316usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(323usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(323usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(323usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(324usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(324usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(324usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(339usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(339usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(339usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(340usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(340usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(340usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(341usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(341usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(341usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(342usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(342usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(342usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(349usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(349usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(349usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(350usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(350usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(350usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(357usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(357usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(357usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(358usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(358usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(358usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(359usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(359usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(359usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(360usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(360usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(360usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(367usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(367usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(367usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(368usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(368usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(368usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(383usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(383usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(383usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(384usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(384usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(384usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(385usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(385usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(385usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(386usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(386usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(386usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(393usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(393usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(393usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(394usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(394usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(394usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(401usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(401usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(401usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(402usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(402usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(402usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(403usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(403usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(403usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(404usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(404usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(404usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(411usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(411usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(411usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(412usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(412usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(412usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(427usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(427usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(427usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(428usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(428usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(428usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(429usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(429usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(429usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(430usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(430usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(430usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(437usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(437usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(437usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(438usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(438usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(438usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(445usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(445usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(445usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(446usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(446usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(446usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(447usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(447usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(447usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(448usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(448usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(448usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(455usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(455usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(455usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(456usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(456usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(456usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(471usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(471usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(471usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(472usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(472usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(472usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(473usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(473usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(473usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(474usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(474usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(474usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(481usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(481usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(481usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(482usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(482usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(482usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(493usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(493usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(493usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(500usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(500usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(500usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(507usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(507usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(507usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(514usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(514usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(514usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(521usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(521usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(521usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(528usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(528usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(528usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(535usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(535usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(535usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(542usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(542usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(542usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(549usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(549usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(549usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(556usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(556usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(556usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(563usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(563usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(563usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(570usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(570usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(570usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(577usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(577usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(577usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(584usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(584usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(584usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(591usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(591usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(591usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(598usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(598usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(598usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(601usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(601usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(601usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(602usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(602usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(602usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(603usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(603usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(603usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(604usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(604usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(604usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(605usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(605usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(605usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(606usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(606usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(606usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(607usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(607usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(607usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(608usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(608usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(608usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(609usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(609usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(609usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(610usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(610usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(610usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(611usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(611usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(611usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(612usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(612usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(612usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(613usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(613usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(613usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(614usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(614usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(614usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(615usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(615usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(615usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(616usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(616usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(616usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(617usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(617usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(617usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(618usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(618usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(618usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(619usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(619usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(619usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(620usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(620usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(620usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(621usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(621usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(621usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(622usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(622usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(622usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(623usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(623usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(623usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(624usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(624usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(624usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(625usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(625usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(625usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(626usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(626usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(626usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(627usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(627usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(627usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(628usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(628usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(628usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(629usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(629usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(629usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(630usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(630usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(630usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(631usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(631usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(631usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(632usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(632usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(632usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(633usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(633usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(633usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(634usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(634usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(634usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(635usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(635usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(635usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(636usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(636usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(636usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(637usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(637usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(637usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(638usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(638usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(638usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(639usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(639usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(639usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(640usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(640usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(640usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(641usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(641usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(641usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(642usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(642usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(642usize, 1744830467usize)];
            let val = eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(643usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(643usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(643usize, 1744830467usize)];
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
    const DESCS: [(usize, usize, usize); 101usize] = [
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
        (2usize, 47usize, 48usize),
        (2usize, 49usize, 50usize),
        (2usize, 51usize, 52usize),
        (2usize, 53usize, 54usize),
        (2usize, 55usize, 56usize),
        (2usize, 57usize, 58usize),
        (2usize, 59usize, 60usize),
        (2usize, 61usize, 62usize),
        (2usize, 63usize, 64usize),
        (2usize, 65usize, 66usize),
        (1usize, 67usize, 0usize),
        (1usize, 68usize, 0usize),
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
        (2usize, 97usize, 98usize),
        (2usize, 99usize, 100usize),
        (2usize, 101usize, 102usize),
        (2usize, 103usize, 104usize),
        (2usize, 105usize, 106usize),
        (2usize, 107usize, 108usize),
        (2usize, 109usize, 110usize),
        (2usize, 111usize, 112usize),
        (2usize, 113usize, 114usize),
        (2usize, 115usize, 116usize),
        (2usize, 117usize, 118usize),
        (2usize, 119usize, 120usize),
        (2usize, 121usize, 122usize),
        (2usize, 123usize, 124usize),
        (2usize, 125usize, 126usize),
        (2usize, 127usize, 128usize),
        (2usize, 129usize, 130usize),
        (2usize, 131usize, 132usize),
        (2usize, 133usize, 134usize),
        (2usize, 135usize, 136usize),
        (2usize, 137usize, 138usize),
        (2usize, 139usize, 140usize),
        (2usize, 141usize, 142usize),
        (2usize, 143usize, 144usize),
        (2usize, 145usize, 146usize),
        (2usize, 147usize, 148usize),
        (2usize, 149usize, 150usize),
        (2usize, 151usize, 152usize),
        (2usize, 153usize, 154usize),
        (2usize, 155usize, 156usize),
        (2usize, 157usize, 158usize),
        (2usize, 159usize, 160usize),
        (2usize, 161usize, 162usize),
        (2usize, 163usize, 164usize),
        (2usize, 165usize, 166usize),
        (2usize, 167usize, 168usize),
        (2usize, 169usize, 170usize),
        (2usize, 171usize, 172usize),
        (1usize, 173usize, 0usize),
        (1usize, 174usize, 0usize),
    ];
    let mut combined = BabyBearExt4::ZERO;
    let mut current_batch = BabyBearExt4::ONE;
    let mut i = 0;
    while i < 101usize {
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
        const SIMPLE_GATES: [(usize, [usize; 4]); 101usize] = [
            (1usize, [0usize, 0usize, 0usize, 0usize]),
            (2usize, [1usize, 3usize, 0usize, 0usize]),
            (2usize, [5usize, 7usize, 0usize, 0usize]),
            (2usize, [9usize, 11usize, 0usize, 0usize]),
            (2usize, [13usize, 15usize, 0usize, 0usize]),
            (2usize, [17usize, 19usize, 0usize, 0usize]),
            (2usize, [21usize, 23usize, 0usize, 0usize]),
            (2usize, [25usize, 27usize, 0usize, 0usize]),
            (2usize, [29usize, 31usize, 0usize, 0usize]),
            (2usize, [33usize, 35usize, 0usize, 0usize]),
            (2usize, [37usize, 39usize, 0usize, 0usize]),
            (2usize, [41usize, 43usize, 0usize, 0usize]),
            (2usize, [2usize, 4usize, 0usize, 0usize]),
            (2usize, [6usize, 8usize, 0usize, 0usize]),
            (2usize, [10usize, 12usize, 0usize, 0usize]),
            (2usize, [14usize, 16usize, 0usize, 0usize]),
            (2usize, [18usize, 20usize, 0usize, 0usize]),
            (2usize, [22usize, 24usize, 0usize, 0usize]),
            (2usize, [26usize, 28usize, 0usize, 0usize]),
            (2usize, [30usize, 32usize, 0usize, 0usize]),
            (2usize, [34usize, 36usize, 0usize, 0usize]),
            (2usize, [38usize, 40usize, 0usize, 0usize]),
            (2usize, [42usize, 44usize, 0usize, 0usize]),
            (7usize, [131usize, 132usize, 133usize, 0usize]),
            (8usize, [129usize, 130usize, 127usize, 128usize]),
            (8usize, [125usize, 126usize, 123usize, 124usize]),
            (8usize, [121usize, 122usize, 119usize, 120usize]),
            (8usize, [117usize, 118usize, 115usize, 116usize]),
            (8usize, [113usize, 114usize, 111usize, 112usize]),
            (8usize, [109usize, 110usize, 107usize, 108usize]),
            (8usize, [105usize, 106usize, 103usize, 104usize]),
            (8usize, [101usize, 102usize, 99usize, 100usize]),
            (8usize, [97usize, 98usize, 95usize, 96usize]),
            (8usize, [93usize, 94usize, 91usize, 92usize]),
            (8usize, [89usize, 90usize, 87usize, 88usize]),
            (8usize, [85usize, 86usize, 83usize, 84usize]),
            (8usize, [81usize, 82usize, 79usize, 80usize]),
            (8usize, [77usize, 78usize, 75usize, 76usize]),
            (8usize, [73usize, 74usize, 71usize, 72usize]),
            (8usize, [69usize, 70usize, 67usize, 68usize]),
            (8usize, [65usize, 66usize, 63usize, 64usize]),
            (8usize, [61usize, 62usize, 59usize, 60usize]),
            (8usize, [57usize, 58usize, 55usize, 56usize]),
            (8usize, [53usize, 54usize, 51usize, 52usize]),
            (8usize, [49usize, 50usize, 47usize, 48usize]),
            (1usize, [45usize, 0usize, 0usize, 0usize]),
            (1usize, [46usize, 0usize, 0usize, 0usize]),
            (7usize, [340usize, 341usize, 342usize, 0usize]),
            (8usize, [338usize, 339usize, 336usize, 337usize]),
            (8usize, [334usize, 335usize, 332usize, 333usize]),
            (8usize, [330usize, 331usize, 328usize, 329usize]),
            (8usize, [326usize, 327usize, 324usize, 325usize]),
            (8usize, [322usize, 323usize, 320usize, 321usize]),
            (8usize, [318usize, 319usize, 316usize, 317usize]),
            (8usize, [314usize, 315usize, 312usize, 313usize]),
            (8usize, [310usize, 311usize, 308usize, 309usize]),
            (8usize, [306usize, 307usize, 304usize, 305usize]),
            (8usize, [302usize, 303usize, 300usize, 301usize]),
            (8usize, [298usize, 299usize, 296usize, 297usize]),
            (8usize, [294usize, 295usize, 292usize, 293usize]),
            (8usize, [290usize, 291usize, 288usize, 289usize]),
            (8usize, [286usize, 287usize, 284usize, 285usize]),
            (8usize, [282usize, 283usize, 280usize, 281usize]),
            (8usize, [278usize, 279usize, 276usize, 277usize]),
            (8usize, [274usize, 275usize, 272usize, 273usize]),
            (8usize, [270usize, 271usize, 268usize, 269usize]),
            (8usize, [266usize, 267usize, 264usize, 265usize]),
            (8usize, [262usize, 263usize, 260usize, 261usize]),
            (8usize, [258usize, 259usize, 256usize, 257usize]),
            (8usize, [254usize, 255usize, 252usize, 253usize]),
            (8usize, [250usize, 251usize, 248usize, 249usize]),
            (8usize, [246usize, 247usize, 244usize, 245usize]),
            (8usize, [242usize, 243usize, 240usize, 241usize]),
            (8usize, [238usize, 239usize, 236usize, 237usize]),
            (8usize, [234usize, 235usize, 232usize, 233usize]),
            (8usize, [230usize, 231usize, 228usize, 229usize]),
            (8usize, [226usize, 227usize, 224usize, 225usize]),
            (8usize, [222usize, 223usize, 220usize, 221usize]),
            (8usize, [218usize, 219usize, 216usize, 217usize]),
            (8usize, [214usize, 215usize, 212usize, 213usize]),
            (8usize, [210usize, 211usize, 208usize, 209usize]),
            (8usize, [206usize, 207usize, 204usize, 205usize]),
            (8usize, [202usize, 203usize, 200usize, 201usize]),
            (8usize, [198usize, 199usize, 196usize, 197usize]),
            (8usize, [194usize, 195usize, 192usize, 193usize]),
            (8usize, [190usize, 191usize, 188usize, 189usize]),
            (8usize, [186usize, 187usize, 184usize, 185usize]),
            (8usize, [182usize, 183usize, 180usize, 181usize]),
            (8usize, [178usize, 179usize, 176usize, 177usize]),
            (8usize, [174usize, 175usize, 172usize, 173usize]),
            (8usize, [170usize, 171usize, 168usize, 169usize]),
            (8usize, [166usize, 167usize, 164usize, 165usize]),
            (8usize, [162usize, 163usize, 160usize, 161usize]),
            (8usize, [158usize, 159usize, 156usize, 157usize]),
            (8usize, [154usize, 155usize, 152usize, 153usize]),
            (8usize, [150usize, 151usize, 148usize, 149usize]),
            (8usize, [146usize, 147usize, 144usize, 145usize]),
            (8usize, [142usize, 143usize, 140usize, 141usize]),
            (8usize, [138usize, 139usize, 136usize, 137usize]),
            (1usize, [134usize, 0usize, 0usize, 0usize]),
            (1usize, [135usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 101usize {
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
    const DESCS: [(usize, usize, usize); 54usize] = [
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
        (1usize, 89usize, 0usize),
        (1usize, 90usize, 0usize),
    ];
    let mut combined = BabyBearExt4::ZERO;
    let mut current_batch = BabyBearExt4::ONE;
    let mut i = 0;
    while i < 54usize {
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
        const SIMPLE_GATES: [(usize, [usize; 4]); 54usize] = [
            (1usize, [0usize, 0usize, 0usize, 0usize]),
            (2usize, [1usize, 2usize, 0usize, 0usize]),
            (2usize, [3usize, 4usize, 0usize, 0usize]),
            (2usize, [5usize, 6usize, 0usize, 0usize]),
            (2usize, [7usize, 8usize, 0usize, 0usize]),
            (2usize, [9usize, 10usize, 0usize, 0usize]),
            (1usize, [11usize, 0usize, 0usize, 0usize]),
            (2usize, [12usize, 13usize, 0usize, 0usize]),
            (2usize, [14usize, 15usize, 0usize, 0usize]),
            (2usize, [16usize, 17usize, 0usize, 0usize]),
            (2usize, [18usize, 19usize, 0usize, 0usize]),
            (2usize, [20usize, 21usize, 0usize, 0usize]),
            (1usize, [22usize, 0usize, 0usize, 0usize]),
            (8usize, [67usize, 68usize, 65usize, 66usize]),
            (8usize, [63usize, 64usize, 61usize, 62usize]),
            (8usize, [59usize, 60usize, 57usize, 58usize]),
            (8usize, [55usize, 56usize, 53usize, 54usize]),
            (8usize, [51usize, 52usize, 49usize, 50usize]),
            (8usize, [47usize, 48usize, 45usize, 46usize]),
            (8usize, [43usize, 44usize, 41usize, 42usize]),
            (8usize, [39usize, 40usize, 37usize, 38usize]),
            (8usize, [35usize, 36usize, 33usize, 34usize]),
            (8usize, [31usize, 32usize, 29usize, 30usize]),
            (8usize, [27usize, 28usize, 25usize, 26usize]),
            (1usize, [23usize, 0usize, 0usize, 0usize]),
            (1usize, [24usize, 0usize, 0usize, 0usize]),
            (8usize, [173usize, 174usize, 171usize, 172usize]),
            (8usize, [169usize, 170usize, 167usize, 168usize]),
            (8usize, [165usize, 166usize, 163usize, 164usize]),
            (8usize, [161usize, 162usize, 159usize, 160usize]),
            (8usize, [157usize, 158usize, 155usize, 156usize]),
            (8usize, [153usize, 154usize, 151usize, 152usize]),
            (8usize, [149usize, 150usize, 147usize, 148usize]),
            (8usize, [145usize, 146usize, 143usize, 144usize]),
            (8usize, [141usize, 142usize, 139usize, 140usize]),
            (8usize, [137usize, 138usize, 135usize, 136usize]),
            (8usize, [133usize, 134usize, 131usize, 132usize]),
            (8usize, [129usize, 130usize, 127usize, 128usize]),
            (8usize, [125usize, 126usize, 123usize, 124usize]),
            (8usize, [121usize, 122usize, 119usize, 120usize]),
            (8usize, [117usize, 118usize, 115usize, 116usize]),
            (8usize, [113usize, 114usize, 111usize, 112usize]),
            (8usize, [109usize, 110usize, 107usize, 108usize]),
            (8usize, [105usize, 106usize, 103usize, 104usize]),
            (8usize, [101usize, 102usize, 99usize, 100usize]),
            (8usize, [97usize, 98usize, 95usize, 96usize]),
            (8usize, [93usize, 94usize, 91usize, 92usize]),
            (8usize, [89usize, 90usize, 87usize, 88usize]),
            (8usize, [85usize, 86usize, 83usize, 84usize]),
            (8usize, [81usize, 82usize, 79usize, 80usize]),
            (8usize, [77usize, 78usize, 75usize, 76usize]),
            (8usize, [73usize, 74usize, 71usize, 72usize]),
            (1usize, [69usize, 0usize, 0usize, 0usize]),
            (1usize, [70usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 54usize {
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
    const DESCS: [(usize, usize, usize); 28usize] = [
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
    while i < 28usize {
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
        const SIMPLE_GATES: [(usize, [usize; 4]); 28usize] = [
            (1usize, [0usize, 0usize, 0usize, 0usize]),
            (2usize, [1usize, 2usize, 0usize, 0usize]),
            (2usize, [3usize, 4usize, 0usize, 0usize]),
            (2usize, [5usize, 6usize, 0usize, 0usize]),
            (2usize, [7usize, 8usize, 0usize, 0usize]),
            (2usize, [9usize, 10usize, 0usize, 0usize]),
            (2usize, [11usize, 12usize, 0usize, 0usize]),
            (8usize, [35usize, 36usize, 33usize, 34usize]),
            (8usize, [31usize, 32usize, 29usize, 30usize]),
            (8usize, [27usize, 28usize, 25usize, 26usize]),
            (8usize, [23usize, 24usize, 21usize, 22usize]),
            (8usize, [19usize, 20usize, 17usize, 18usize]),
            (8usize, [15usize, 16usize, 13usize, 14usize]),
            (8usize, [89usize, 90usize, 87usize, 88usize]),
            (8usize, [85usize, 86usize, 83usize, 84usize]),
            (8usize, [81usize, 82usize, 79usize, 80usize]),
            (8usize, [77usize, 78usize, 75usize, 76usize]),
            (8usize, [73usize, 74usize, 71usize, 72usize]),
            (8usize, [69usize, 70usize, 67usize, 68usize]),
            (8usize, [65usize, 66usize, 63usize, 64usize]),
            (8usize, [61usize, 62usize, 59usize, 60usize]),
            (8usize, [57usize, 58usize, 55usize, 56usize]),
            (8usize, [53usize, 54usize, 51usize, 52usize]),
            (8usize, [49usize, 50usize, 47usize, 48usize]),
            (8usize, [45usize, 46usize, 43usize, 44usize]),
            (8usize, [41usize, 42usize, 39usize, 40usize]),
            (1usize, [37usize, 0usize, 0usize, 0usize]),
            (1usize, [38usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 28usize {
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
    const DESCS: [(usize, usize, usize); 15usize] = [
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
        (2usize, 23usize, 24usize),
    ];
    let mut combined = BabyBearExt4::ZERO;
    let mut current_batch = BabyBearExt4::ONE;
    let mut i = 0;
    while i < 15usize {
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
        const SIMPLE_GATES: [(usize, [usize; 4]); 15usize] = [
            (1usize, [0usize, 0usize, 0usize, 0usize]),
            (2usize, [1usize, 2usize, 0usize, 0usize]),
            (1usize, [3usize, 0usize, 0usize, 0usize]),
            (2usize, [4usize, 5usize, 0usize, 0usize]),
            (1usize, [6usize, 0usize, 0usize, 0usize]),
            (8usize, [17usize, 18usize, 15usize, 16usize]),
            (8usize, [13usize, 14usize, 11usize, 12usize]),
            (8usize, [9usize, 10usize, 7usize, 8usize]),
            (8usize, [45usize, 46usize, 43usize, 44usize]),
            (8usize, [41usize, 42usize, 39usize, 40usize]),
            (8usize, [37usize, 38usize, 35usize, 36usize]),
            (8usize, [33usize, 34usize, 31usize, 32usize]),
            (8usize, [29usize, 30usize, 27usize, 28usize]),
            (8usize, [25usize, 26usize, 23usize, 24usize]),
            (8usize, [21usize, 22usize, 19usize, 20usize]),
        ];
        let mut _sg = 0;
        while _sg < 15usize {
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
    const DESCS: [(usize, usize, usize); 11usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (1usize, 2usize, 0usize),
        (2usize, 3usize, 4usize),
        (1usize, 5usize, 0usize),
        (1usize, 6usize, 0usize),
        (2usize, 7usize, 8usize),
        (2usize, 9usize, 10usize),
        (2usize, 11usize, 12usize),
        (1usize, 13usize, 0usize),
        (1usize, 14usize, 0usize),
    ];
    let mut combined = BabyBearExt4::ZERO;
    let mut current_batch = BabyBearExt4::ONE;
    let mut i = 0;
    while i < 11usize {
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
        const SIMPLE_GATES: [(usize, [usize; 4]); 11usize] = [
            (1usize, [0usize, 0usize, 0usize, 0usize]),
            (2usize, [1usize, 2usize, 0usize, 0usize]),
            (2usize, [3usize, 4usize, 0usize, 0usize]),
            (8usize, [9usize, 10usize, 7usize, 8usize]),
            (1usize, [5usize, 0usize, 0usize, 0usize]),
            (1usize, [6usize, 0usize, 0usize, 0usize]),
            (8usize, [23usize, 24usize, 21usize, 22usize]),
            (8usize, [19usize, 20usize, 17usize, 18usize]),
            (8usize, [15usize, 16usize, 13usize, 14usize]),
            (1usize, [11usize, 0usize, 0usize, 0usize]),
            (1usize, [12usize, 0usize, 0usize, 0usize]),
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
    acc
}
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_6_compute_claim(
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
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_6_final_step_accumulator(
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
            (8usize, [13usize, 14usize, 11usize, 12usize]),
            (8usize, [9usize, 10usize, 7usize, 8usize]),
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
#[allow(unused_variables)]
unsafe fn layer_7_compute_claim(
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
unsafe fn layer_7_final_step_accumulator(
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
        const DIM_REDUCE_INDICES_8: [usize; 6usize] =
            [2usize, 3usize, 4usize, 5usize, 0usize, 1usize];
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
            let initial_claim = layer_7_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    7usize,
                )?;
            let mut fc_len = 19usize;
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
                let f = layer_7_final_step_accumulator(
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
                    7usize,
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
            let initial_claim = layer_6_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    6usize,
                )?;
            let mut fc_len = 19usize;
            let data_words = 15usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(15usize);
                let f = layer_6_final_step_accumulator(
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
                    6usize,
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
            let initial_claim = layer_5_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    5usize,
                )?;
            let mut fc_len = 19usize;
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
            fold_standard_claims::<25usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    4usize,
                )?;
            let mut fc_len = 19usize;
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
            fold_standard_claims::<47usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    3usize,
                )?;
            let mut fc_len = 19usize;
            let data_words = 91usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(91usize);
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
            fold_standard_claims::<91usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    2usize,
                )?;
            let mut fc_len = 19usize;
            let data_words = 175usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(175usize);
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
            fold_standard_claims::<175usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    1usize,
                )?;
            let mut fc_len = 19usize;
            let data_words = 343usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(343usize);
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
            fold_standard_claims::<343usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    &mut ts,
                    initial_claim,
                    &mut state.prev_point,
                    0usize,
                )?;
            let mut fc_len = 19usize;
            let data_words = 876usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(876usize);
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
            fold_standard_claims::<876usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
