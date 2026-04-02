use super::common::{
    commit_field_els, dot_eq, draw_field_els_into, fold_standard_claims, make_eq_poly,
    read_field_el, read_field_els, verify_final_step_check, verify_sumcheck_rounds,
};
use super::constants::*;
use verifier_common::blake2s_u32::{
    AlignedArray64, DelegatedBlake2sState, BLAKE2S_DIGEST_SIZE_U32_WORDS,
};
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::field::{Field, FieldExtension, PrimeField};
use verifier_common::field_ops;
use verifier_common::gkr::{
    commit_eval_buffer, read_eval_data_from_nds, GKRVerificationError, GKRVerifierOutput,
    LayerState, LazyVec,
};
use verifier_common::non_determinism_source::NonDeterminismSource;
use verifier_common::transcript::Blake2sTranscript;
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn layer_0_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 55usize] = [
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
    ];
    let mut combined = BabyBearExt4::ZERO;
    let mut current_batch = BabyBearExt4::ONE;
    let mut i = 0;
    while i < 55usize {
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
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(usize, [usize; 4]); 54usize] = [
            (1usize, [227usize, 0usize, 0usize, 0usize]),
            (2usize, [231usize, 232usize, 0usize, 0usize]),
            (2usize, [233usize, 234usize, 0usize, 0usize]),
            (2usize, [235usize, 236usize, 0usize, 0usize]),
            (2usize, [237usize, 238usize, 0usize, 0usize]),
            (2usize, [239usize, 240usize, 0usize, 0usize]),
            (2usize, [241usize, 242usize, 0usize, 0usize]),
            (2usize, [243usize, 244usize, 0usize, 0usize]),
            (2usize, [245usize, 246usize, 0usize, 0usize]),
            (2usize, [247usize, 248usize, 0usize, 0usize]),
            (2usize, [249usize, 250usize, 0usize, 0usize]),
            (2usize, [251usize, 252usize, 0usize, 0usize]),
            (2usize, [253usize, 254usize, 0usize, 0usize]),
            (2usize, [255usize, 256usize, 0usize, 0usize]),
            (2usize, [257usize, 258usize, 0usize, 0usize]),
            (1usize, [259usize, 0usize, 0usize, 0usize]),
            (1usize, [260usize, 0usize, 0usize, 0usize]),
            (6usize, [228usize, 173usize, 230usize, 0usize]),
            (5usize, [229usize, 261usize, 0usize, 0usize]),
            (5usize, [262usize, 263usize, 0usize, 0usize]),
            (5usize, [264usize, 265usize, 0usize, 0usize]),
            (5usize, [266usize, 267usize, 0usize, 0usize]),
            (5usize, [268usize, 269usize, 0usize, 0usize]),
            (5usize, [270usize, 271usize, 0usize, 0usize]),
            (5usize, [272usize, 273usize, 0usize, 0usize]),
            (5usize, [274usize, 275usize, 0usize, 0usize]),
            (5usize, [276usize, 277usize, 0usize, 0usize]),
            (5usize, [278usize, 279usize, 0usize, 0usize]),
            (5usize, [280usize, 281usize, 0usize, 0usize]),
            (5usize, [282usize, 283usize, 0usize, 0usize]),
            (5usize, [284usize, 285usize, 0usize, 0usize]),
            (5usize, [286usize, 287usize, 0usize, 0usize]),
            (1usize, [288usize, 0usize, 0usize, 0usize]),
            (6usize, [289usize, 174usize, 290usize, 0usize]),
            (5usize, [291usize, 292usize, 0usize, 0usize]),
            (5usize, [293usize, 294usize, 0usize, 0usize]),
            (5usize, [295usize, 296usize, 0usize, 0usize]),
            (5usize, [297usize, 298usize, 0usize, 0usize]),
            (5usize, [299usize, 300usize, 0usize, 0usize]),
            (5usize, [301usize, 302usize, 0usize, 0usize]),
            (5usize, [303usize, 304usize, 0usize, 0usize]),
            (5usize, [305usize, 306usize, 0usize, 0usize]),
            (5usize, [307usize, 308usize, 0usize, 0usize]),
            (5usize, [309usize, 310usize, 0usize, 0usize]),
            (5usize, [311usize, 312usize, 0usize, 0usize]),
            (5usize, [313usize, 314usize, 0usize, 0usize]),
            (5usize, [315usize, 316usize, 0usize, 0usize]),
            (5usize, [317usize, 318usize, 0usize, 0usize]),
            (5usize, [319usize, 320usize, 0usize, 0usize]),
            (5usize, [321usize, 322usize, 0usize, 0usize]),
            (5usize, [323usize, 324usize, 0usize, 0usize]),
            (5usize, [325usize, 326usize, 0usize, 0usize]),
            (5usize, [327usize, 328usize, 0usize, 0usize]),
            (5usize, [329usize, 330usize, 0usize, 0usize]),
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
                _ => {}
            }
            _sg += 1;
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let val = {
                let mut result: BabyBearExt4 = BabyBearExt4::ZERO;
                {
                    const CK_CONST: [(u32, usize); 4usize] = [
                        (536853436u32, 15usize),
                        (671036075u32, 16usize),
                        (805218714u32, 17usize),
                        (939401353u32, 18usize),
                    ];
                    let mut _i: usize = 0;
                    while _i < 4usize {
                        let (coeff, pow) = CK_CONST[_i];
                        let mut t: BabyBearExt4 = *challenge_powers.get_unchecked(pow);
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(coeff),
                        );
                        field_ops::add_assign(&mut result, &t);
                        _i += 1;
                    }
                }
                {
                    const CK_LIN_GROUPS: [(usize, usize, usize); 115usize] = [
                        (0usize, 0usize, 1usize),
                        (1usize, 1usize, 1usize),
                        (2usize, 2usize, 1usize),
                        (3usize, 3usize, 16usize),
                        (4usize, 19usize, 1usize),
                        (5usize, 20usize, 1usize),
                        (6usize, 21usize, 7usize),
                        (7usize, 28usize, 5usize),
                        (8usize, 33usize, 17usize),
                        (9usize, 50usize, 1usize),
                        (10usize, 51usize, 1usize),
                        (11usize, 52usize, 1usize),
                        (12usize, 53usize, 1usize),
                        (13usize, 54usize, 1usize),
                        (14usize, 55usize, 1usize),
                        (15usize, 56usize, 2usize),
                        (16usize, 58usize, 2usize),
                        (17usize, 60usize, 2usize),
                        (18usize, 62usize, 2usize),
                        (19usize, 64usize, 6usize),
                        (20usize, 70usize, 2usize),
                        (21usize, 72usize, 2usize),
                        (22usize, 74usize, 2usize),
                        (23usize, 76usize, 2usize),
                        (24usize, 78usize, 2usize),
                        (25usize, 80usize, 2usize),
                        (26usize, 82usize, 2usize),
                        (27usize, 84usize, 2usize),
                        (28usize, 86usize, 2usize),
                        (29usize, 88usize, 2usize),
                        (30usize, 90usize, 2usize),
                        (31usize, 92usize, 2usize),
                        (32usize, 94usize, 6usize),
                        (33usize, 100usize, 2usize),
                        (34usize, 102usize, 2usize),
                        (35usize, 104usize, 2usize),
                        (36usize, 106usize, 2usize),
                        (37usize, 108usize, 2usize),
                        (38usize, 110usize, 2usize),
                        (39usize, 112usize, 2usize),
                        (40usize, 114usize, 2usize),
                        (41usize, 116usize, 2usize),
                        (42usize, 118usize, 2usize),
                        (43usize, 120usize, 2usize),
                        (44usize, 122usize, 2usize),
                        (45usize, 124usize, 6usize),
                        (46usize, 130usize, 2usize),
                        (47usize, 132usize, 2usize),
                        (48usize, 134usize, 2usize),
                        (49usize, 136usize, 2usize),
                        (50usize, 138usize, 2usize),
                        (51usize, 140usize, 2usize),
                        (52usize, 142usize, 2usize),
                        (53usize, 144usize, 2usize),
                        (54usize, 146usize, 2usize),
                        (55usize, 148usize, 2usize),
                        (56usize, 150usize, 2usize),
                        (57usize, 152usize, 2usize),
                        (58usize, 154usize, 6usize),
                        (59usize, 160usize, 2usize),
                        (60usize, 162usize, 2usize),
                        (61usize, 164usize, 2usize),
                        (62usize, 166usize, 2usize),
                        (63usize, 168usize, 2usize),
                        (64usize, 170usize, 2usize),
                        (65usize, 172usize, 2usize),
                        (66usize, 174usize, 2usize),
                        (67usize, 176usize, 2usize),
                        (68usize, 178usize, 2usize),
                        (69usize, 180usize, 2usize),
                        (70usize, 182usize, 2usize),
                        (71usize, 184usize, 6usize),
                        (72usize, 190usize, 2usize),
                        (73usize, 192usize, 2usize),
                        (74usize, 194usize, 2usize),
                        (75usize, 196usize, 2usize),
                        (76usize, 198usize, 2usize),
                        (77usize, 200usize, 2usize),
                        (78usize, 202usize, 2usize),
                        (79usize, 204usize, 2usize),
                        (80usize, 206usize, 2usize),
                        (81usize, 208usize, 2usize),
                        (82usize, 210usize, 2usize),
                        (83usize, 212usize, 2usize),
                        (156usize, 214usize, 1usize),
                        (157usize, 215usize, 1usize),
                        (158usize, 216usize, 1usize),
                        (159usize, 217usize, 1usize),
                        (160usize, 218usize, 1usize),
                        (161usize, 219usize, 1usize),
                        (162usize, 220usize, 1usize),
                        (163usize, 221usize, 1usize),
                        (164usize, 222usize, 1usize),
                        (165usize, 223usize, 1usize),
                        (166usize, 224usize, 1usize),
                        (167usize, 225usize, 1usize),
                        (168usize, 226usize, 1usize),
                        (169usize, 227usize, 1usize),
                        (170usize, 228usize, 1usize),
                        (171usize, 229usize, 1usize),
                        (172usize, 230usize, 1usize),
                        (173usize, 231usize, 1usize),
                        (174usize, 232usize, 1usize),
                        (175usize, 233usize, 1usize),
                        (176usize, 234usize, 1usize),
                        (177usize, 235usize, 1usize),
                        (178usize, 236usize, 1usize),
                        (179usize, 237usize, 1usize),
                        (180usize, 238usize, 1usize),
                        (181usize, 239usize, 1usize),
                        (182usize, 240usize, 1usize),
                        (183usize, 241usize, 1usize),
                        (184usize, 242usize, 1usize),
                        (185usize, 243usize, 1usize),
                        (186usize, 244usize, 1usize),
                    ];
                    const CK_LIN_TERMS: [(u32, usize); 245usize] = [
                        (1744830467u32, 227usize),
                        (268435454u32, 176usize),
                        (268435454u32, 178usize),
                        (268435454u32, 1usize),
                        (536870908u32, 2usize),
                        (805306362u32, 3usize),
                        (1073741816u32, 4usize),
                        (1342177270u32, 5usize),
                        (1610612724u32, 6usize),
                        (134217711u32, 8usize),
                        (268435422u32, 9usize),
                        (402653133u32, 10usize),
                        (536870844u32, 11usize),
                        (1073741688u32, 12usize),
                        (134217455u32, 13usize),
                        (268434910u32, 14usize),
                        (536869820u32, 15usize),
                        (1073739640u32, 16usize),
                        (1744830467u32, 175usize),
                        (1744830467u32, 227usize),
                        (1744830467u32, 227usize),
                        (268435454u32, 0usize),
                        (268435454u32, 1usize),
                        (268435454u32, 2usize),
                        (268435454u32, 3usize),
                        (268435454u32, 4usize),
                        (268435454u32, 5usize),
                        (268435454u32, 6usize),
                        (268435454u32, 7usize),
                        (268435454u32, 8usize),
                        (268435454u32, 9usize),
                        (268435454u32, 10usize),
                        (268435454u32, 11usize),
                        (134217711u32, 0usize),
                        (536870908u32, 1usize),
                        (805306362u32, 2usize),
                        (939524073u32, 3usize),
                        (1207959527u32, 4usize),
                        (1610612724u32, 5usize),
                        (1476394981u32, 6usize),
                        (134217711u32, 8usize),
                        (268435422u32, 9usize),
                        (402653133u32, 10usize),
                        (536870844u32, 11usize),
                        (1073741688u32, 12usize),
                        (134217455u32, 13usize),
                        (268434910u32, 14usize),
                        (536869820u32, 15usize),
                        (1073739640u32, 16usize),
                        (1744830467u32, 177usize),
                        (1744830467u32, 17usize),
                        (1744830467u32, 18usize),
                        (1744830467u32, 19usize),
                        (1744830467u32, 20usize),
                        (1744830467u32, 21usize),
                        (1744830467u32, 22usize),
                        (536870364u32, 22usize),
                        (1744830467u32, 23usize),
                        (536870364u32, 22usize),
                        (1744830467u32, 24usize),
                        (536870364u32, 22usize),
                        (1744830467u32, 25usize),
                        (536870364u32, 22usize),
                        (1744830467u32, 26usize),
                        (268435454u32, 4usize),
                        (1744830467u32, 17usize),
                        (1744830467u32, 18usize),
                        (1744830467u32, 19usize),
                        (1744830467u32, 20usize),
                        (1744830467u32, 21usize),
                        (268435454u32, 39usize),
                        (268434910u32, 40usize),
                        (268435454u32, 47usize),
                        (268434910u32, 48usize),
                        (268435454u32, 55usize),
                        (268434910u32, 56usize),
                        (268435454u32, 41usize),
                        (268434910u32, 42usize),
                        (268435454u32, 49usize),
                        (268434910u32, 50usize),
                        (268435454u32, 57usize),
                        (268434910u32, 58usize),
                        (268435454u32, 43usize),
                        (268434910u32, 44usize),
                        (268435454u32, 51usize),
                        (268434910u32, 52usize),
                        (268435454u32, 59usize),
                        (268434910u32, 60usize),
                        (268435454u32, 45usize),
                        (268434910u32, 46usize),
                        (268435454u32, 53usize),
                        (268434910u32, 54usize),
                        (268435454u32, 61usize),
                        (268434910u32, 62usize),
                        (268435454u32, 4usize),
                        (1744830467u32, 17usize),
                        (1744830467u32, 18usize),
                        (1744830467u32, 19usize),
                        (1744830467u32, 20usize),
                        (1744830467u32, 21usize),
                        (268435454u32, 63usize),
                        (268434910u32, 64usize),
                        (268435454u32, 71usize),
                        (268434910u32, 72usize),
                        (268435454u32, 79usize),
                        (268434910u32, 80usize),
                        (268435454u32, 65usize),
                        (268434910u32, 66usize),
                        (268435454u32, 73usize),
                        (268434910u32, 74usize),
                        (268435454u32, 81usize),
                        (268434910u32, 82usize),
                        (268435454u32, 67usize),
                        (268434910u32, 68usize),
                        (268435454u32, 75usize),
                        (268434910u32, 76usize),
                        (268435454u32, 83usize),
                        (268434910u32, 84usize),
                        (268435454u32, 69usize),
                        (268434910u32, 70usize),
                        (268435454u32, 77usize),
                        (268434910u32, 78usize),
                        (268435454u32, 85usize),
                        (268434910u32, 86usize),
                        (268435454u32, 4usize),
                        (1744830467u32, 17usize),
                        (1744830467u32, 18usize),
                        (1744830467u32, 19usize),
                        (1744830467u32, 20usize),
                        (1744830467u32, 21usize),
                        (268435454u32, 87usize),
                        (268434910u32, 88usize),
                        (268435454u32, 95usize),
                        (268434910u32, 96usize),
                        (268435454u32, 103usize),
                        (268434910u32, 104usize),
                        (268435454u32, 89usize),
                        (268434910u32, 90usize),
                        (268435454u32, 97usize),
                        (268434910u32, 98usize),
                        (268435454u32, 105usize),
                        (268434910u32, 106usize),
                        (268435454u32, 91usize),
                        (268434910u32, 92usize),
                        (268435454u32, 99usize),
                        (268434910u32, 100usize),
                        (268435454u32, 107usize),
                        (268434910u32, 108usize),
                        (268435454u32, 93usize),
                        (268434910u32, 94usize),
                        (268435454u32, 101usize),
                        (268434910u32, 102usize),
                        (268435454u32, 109usize),
                        (268434910u32, 110usize),
                        (268435454u32, 4usize),
                        (1744830467u32, 17usize),
                        (1744830467u32, 18usize),
                        (1744830467u32, 19usize),
                        (1744830467u32, 20usize),
                        (1744830467u32, 21usize),
                        (268435454u32, 111usize),
                        (268434910u32, 112usize),
                        (268435454u32, 119usize),
                        (268434910u32, 120usize),
                        (268435454u32, 127usize),
                        (268434910u32, 128usize),
                        (268435454u32, 113usize),
                        (268434910u32, 114usize),
                        (268435454u32, 121usize),
                        (268434910u32, 122usize),
                        (268435454u32, 129usize),
                        (268434910u32, 130usize),
                        (268435454u32, 115usize),
                        (268434910u32, 116usize),
                        (268435454u32, 123usize),
                        (268434910u32, 124usize),
                        (268435454u32, 131usize),
                        (268434910u32, 132usize),
                        (268435454u32, 117usize),
                        (268434910u32, 118usize),
                        (268435454u32, 125usize),
                        (268434910u32, 126usize),
                        (268435454u32, 133usize),
                        (268434910u32, 134usize),
                        (268435454u32, 4usize),
                        (1744830467u32, 17usize),
                        (1744830467u32, 18usize),
                        (1744830467u32, 19usize),
                        (1744830467u32, 20usize),
                        (1744830467u32, 21usize),
                        (268435454u32, 135usize),
                        (268434910u32, 136usize),
                        (268435454u32, 143usize),
                        (268434910u32, 144usize),
                        (268435454u32, 151usize),
                        (268434910u32, 152usize),
                        (268435454u32, 137usize),
                        (268434910u32, 138usize),
                        (268435454u32, 145usize),
                        (268434910u32, 146usize),
                        (268435454u32, 153usize),
                        (268434910u32, 154usize),
                        (268435454u32, 139usize),
                        (268434910u32, 140usize),
                        (268435454u32, 147usize),
                        (268434910u32, 148usize),
                        (268435454u32, 155usize),
                        (268434910u32, 156usize),
                        (268435454u32, 141usize),
                        (268434910u32, 142usize),
                        (268435454u32, 149usize),
                        (268434910u32, 150usize),
                        (268435454u32, 157usize),
                        (268434910u32, 158usize),
                        (1744830467u32, 0usize),
                        (1744830467u32, 1usize),
                        (1744830467u32, 2usize),
                        (1744830467u32, 3usize),
                        (1744830467u32, 4usize),
                        (1744830467u32, 5usize),
                        (1744830467u32, 6usize),
                        (1744830467u32, 7usize),
                        (1744830467u32, 8usize),
                        (1744830467u32, 9usize),
                        (1744830467u32, 10usize),
                        (1744830467u32, 11usize),
                        (1744830467u32, 12usize),
                        (1744830467u32, 13usize),
                        (1744830467u32, 14usize),
                        (1744830467u32, 15usize),
                        (1744830467u32, 16usize),
                        (1744830467u32, 159usize),
                        (1744830467u32, 160usize),
                        (1744830467u32, 161usize),
                        (1744830467u32, 162usize),
                        (1744830467u32, 163usize),
                        (1744830467u32, 164usize),
                        (1744830467u32, 165usize),
                        (1744830467u32, 166usize),
                        (1744830467u32, 167usize),
                        (1744830467u32, 168usize),
                        (1744830467u32, 169usize),
                        (1744830467u32, 170usize),
                        (1744830467u32, 171usize),
                        (1744830467u32, 172usize),
                    ];
                    let mut _g: usize = 0;
                    while _g < 115usize {
                        let (pow, term_start, term_count) = CK_LIN_GROUPS[_g];
                        let mut inner_sum: BabyBearExt4 = BabyBearExt4::ZERO;
                        let mut _t: usize = 0;
                        while _t < term_count {
                            let (coeff, eval_idx) = CK_LIN_TERMS[term_start + _t];
                            let mut val = evals.get_unchecked(eval_idx)[j];
                            field_ops::mul_assign_by_base(
                                &mut val,
                                &BabyBearField::from_reduced_raw_repr(coeff),
                            );
                            field_ops::add_assign(&mut inner_sum, &val);
                            _t += 1;
                        }
                        let mut t: BabyBearExt4 = *challenge_powers.get_unchecked(pow);
                        field_ops::mul_assign(&mut t, &inner_sum);
                        field_ops::add_assign(&mut result, &t);
                        _g += 1;
                    }
                }
                {
                    const CK_QUAD_GROUPS: [(usize, usize, usize); 175usize] = [
                        (0usize, 0usize, 1usize),
                        (4usize, 1usize, 7usize),
                        (5usize, 8usize, 5usize),
                        (6usize, 13usize, 7usize),
                        (7usize, 20usize, 5usize),
                        (8usize, 25usize, 4usize),
                        (9usize, 29usize, 1usize),
                        (10usize, 30usize, 1usize),
                        (11usize, 31usize, 1usize),
                        (12usize, 32usize, 1usize),
                        (13usize, 33usize, 1usize),
                        (14usize, 34usize, 5usize),
                        (20usize, 39usize, 41usize),
                        (21usize, 80usize, 18usize),
                        (22usize, 98usize, 26usize),
                        (23usize, 124usize, 55usize),
                        (24usize, 179usize, 18usize),
                        (25usize, 197usize, 33usize),
                        (26usize, 230usize, 55usize),
                        (27usize, 285usize, 18usize),
                        (28usize, 303usize, 35usize),
                        (29usize, 338usize, 55usize),
                        (30usize, 393usize, 18usize),
                        (31usize, 411usize, 35usize),
                        (33usize, 446usize, 34usize),
                        (34usize, 480usize, 17usize),
                        (35usize, 497usize, 26usize),
                        (36usize, 523usize, 46usize),
                        (37usize, 569usize, 17usize),
                        (38usize, 586usize, 27usize),
                        (39usize, 613usize, 46usize),
                        (40usize, 659usize, 17usize),
                        (41usize, 676usize, 31usize),
                        (42usize, 707usize, 46usize),
                        (43usize, 753usize, 17usize),
                        (44usize, 770usize, 31usize),
                        (46usize, 801usize, 34usize),
                        (47usize, 835usize, 17usize),
                        (48usize, 852usize, 25usize),
                        (49usize, 877usize, 46usize),
                        (50usize, 923usize, 17usize),
                        (51usize, 940usize, 29usize),
                        (52usize, 969usize, 46usize),
                        (53usize, 1015usize, 17usize),
                        (54usize, 1032usize, 31usize),
                        (55usize, 1063usize, 46usize),
                        (56usize, 1109usize, 17usize),
                        (57usize, 1126usize, 31usize),
                        (59usize, 1157usize, 34usize),
                        (60usize, 1191usize, 17usize),
                        (61usize, 1208usize, 25usize),
                        (62usize, 1233usize, 46usize),
                        (63usize, 1279usize, 17usize),
                        (64usize, 1296usize, 29usize),
                        (65usize, 1325usize, 46usize),
                        (66usize, 1371usize, 17usize),
                        (67usize, 1388usize, 31usize),
                        (68usize, 1419usize, 46usize),
                        (69usize, 1465usize, 17usize),
                        (70usize, 1482usize, 31usize),
                        (72usize, 1513usize, 27usize),
                        (73usize, 1540usize, 16usize),
                        (74usize, 1556usize, 21usize),
                        (75usize, 1577usize, 37usize),
                        (76usize, 1614usize, 16usize),
                        (77usize, 1630usize, 23usize),
                        (78usize, 1653usize, 37usize),
                        (79usize, 1690usize, 16usize),
                        (80usize, 1706usize, 27usize),
                        (81usize, 1733usize, 37usize),
                        (82usize, 1770usize, 16usize),
                        (83usize, 1786usize, 27usize),
                        (84usize, 1813usize, 2usize),
                        (85usize, 1815usize, 2usize),
                        (86usize, 1817usize, 2usize),
                        (87usize, 1819usize, 2usize),
                        (88usize, 1821usize, 2usize),
                        (89usize, 1823usize, 2usize),
                        (90usize, 1825usize, 2usize),
                        (91usize, 1827usize, 2usize),
                        (92usize, 1829usize, 2usize),
                        (93usize, 1831usize, 2usize),
                        (94usize, 1833usize, 2usize),
                        (95usize, 1835usize, 2usize),
                        (96usize, 1837usize, 2usize),
                        (97usize, 1839usize, 2usize),
                        (98usize, 1841usize, 2usize),
                        (99usize, 1843usize, 2usize),
                        (100usize, 1845usize, 2usize),
                        (101usize, 1847usize, 2usize),
                        (102usize, 1849usize, 2usize),
                        (103usize, 1851usize, 2usize),
                        (104usize, 1853usize, 2usize),
                        (105usize, 1855usize, 2usize),
                        (106usize, 1857usize, 2usize),
                        (107usize, 1859usize, 2usize),
                        (108usize, 1861usize, 2usize),
                        (109usize, 1863usize, 2usize),
                        (110usize, 1865usize, 2usize),
                        (111usize, 1867usize, 2usize),
                        (112usize, 1869usize, 2usize),
                        (113usize, 1871usize, 2usize),
                        (114usize, 1873usize, 2usize),
                        (115usize, 1875usize, 2usize),
                        (116usize, 1877usize, 2usize),
                        (117usize, 1879usize, 2usize),
                        (118usize, 1881usize, 2usize),
                        (119usize, 1883usize, 2usize),
                        (120usize, 1885usize, 2usize),
                        (121usize, 1887usize, 2usize),
                        (122usize, 1889usize, 2usize),
                        (123usize, 1891usize, 2usize),
                        (124usize, 1893usize, 2usize),
                        (125usize, 1895usize, 2usize),
                        (126usize, 1897usize, 2usize),
                        (127usize, 1899usize, 2usize),
                        (128usize, 1901usize, 2usize),
                        (129usize, 1903usize, 2usize),
                        (130usize, 1905usize, 2usize),
                        (131usize, 1907usize, 2usize),
                        (132usize, 1909usize, 2usize),
                        (133usize, 1911usize, 2usize),
                        (134usize, 1913usize, 2usize),
                        (135usize, 1915usize, 2usize),
                        (136usize, 1917usize, 2usize),
                        (137usize, 1919usize, 2usize),
                        (138usize, 1921usize, 2usize),
                        (139usize, 1923usize, 2usize),
                        (140usize, 1925usize, 2usize),
                        (141usize, 1927usize, 2usize),
                        (142usize, 1929usize, 2usize),
                        (143usize, 1931usize, 2usize),
                        (144usize, 1933usize, 2usize),
                        (145usize, 1935usize, 2usize),
                        (146usize, 1937usize, 2usize),
                        (147usize, 1939usize, 2usize),
                        (148usize, 1941usize, 2usize),
                        (149usize, 1943usize, 2usize),
                        (150usize, 1945usize, 2usize),
                        (151usize, 1947usize, 2usize),
                        (152usize, 1949usize, 2usize),
                        (153usize, 1951usize, 2usize),
                        (154usize, 1953usize, 2usize),
                        (155usize, 1955usize, 2usize),
                        (156usize, 1957usize, 1usize),
                        (157usize, 1958usize, 1usize),
                        (158usize, 1959usize, 1usize),
                        (159usize, 1960usize, 1usize),
                        (160usize, 1961usize, 1usize),
                        (161usize, 1962usize, 1usize),
                        (162usize, 1963usize, 1usize),
                        (163usize, 1964usize, 1usize),
                        (164usize, 1965usize, 1usize),
                        (165usize, 1966usize, 1usize),
                        (166usize, 1967usize, 1usize),
                        (167usize, 1968usize, 1usize),
                        (168usize, 1969usize, 1usize),
                        (169usize, 1970usize, 1usize),
                        (170usize, 1971usize, 1usize),
                        (171usize, 1972usize, 1usize),
                        (172usize, 1973usize, 1usize),
                        (173usize, 1974usize, 1usize),
                        (174usize, 1975usize, 1usize),
                        (175usize, 1976usize, 1usize),
                        (176usize, 1977usize, 1usize),
                        (177usize, 1978usize, 1usize),
                        (178usize, 1979usize, 1usize),
                        (179usize, 1980usize, 1usize),
                        (180usize, 1981usize, 1usize),
                        (181usize, 1982usize, 1usize),
                        (182usize, 1983usize, 1usize),
                        (183usize, 1984usize, 1usize),
                        (184usize, 1985usize, 1usize),
                        (185usize, 1986usize, 1usize),
                        (186usize, 1987usize, 1usize),
                    ];
                    const CK_QUAD_TERMS: [(u32, usize, usize); 1988usize] = [
                        (268435454u32, 227usize, 227usize),
                        (268435454u32, 227usize, 0usize),
                        (268435454u32, 227usize, 1usize),
                        (268435454u32, 227usize, 2usize),
                        (268435454u32, 227usize, 3usize),
                        (268435454u32, 227usize, 4usize),
                        (268435454u32, 227usize, 5usize),
                        (268435454u32, 227usize, 6usize),
                        (268435454u32, 227usize, 7usize),
                        (268435454u32, 227usize, 8usize),
                        (268435454u32, 227usize, 9usize),
                        (268435454u32, 227usize, 10usize),
                        (268435454u32, 227usize, 11usize),
                        (1744830467u32, 227usize, 0usize),
                        (1744830467u32, 227usize, 1usize),
                        (1744830467u32, 227usize, 2usize),
                        (1744830467u32, 227usize, 3usize),
                        (1744830467u32, 227usize, 4usize),
                        (1744830467u32, 227usize, 5usize),
                        (1744830467u32, 227usize, 6usize),
                        (1744830467u32, 227usize, 7usize),
                        (1744830467u32, 227usize, 8usize),
                        (1744830467u32, 227usize, 9usize),
                        (1744830467u32, 227usize, 10usize),
                        (1744830467u32, 227usize, 11usize),
                        (1610612820u32, 0usize, 11usize),
                        (1610612820u32, 3usize, 11usize),
                        (1610612820u32, 4usize, 11usize),
                        (1073741784u32, 6usize, 11usize),
                        (268435454u32, 4usize, 7usize),
                        (268435454u32, 4usize, 8usize),
                        (268435454u32, 4usize, 9usize),
                        (268435454u32, 4usize, 10usize),
                        (268435454u32, 4usize, 11usize),
                        (268435454u32, 7usize, 12usize),
                        (536870908u32, 7usize, 13usize),
                        (1073741816u32, 7usize, 14usize),
                        (134217711u32, 7usize, 15usize),
                        (268435422u32, 7usize, 16usize),
                        (1744970275u32, 1usize, 1usize),
                        (1476674629u32, 1usize, 2usize),
                        (1744970275u32, 1usize, 17usize),
                        (1476674629u32, 1usize, 18usize),
                        (2097152u32, 1usize, 19usize),
                        (538688444u32, 1usize, 20usize),
                        (806984090u32, 1usize, 21usize),
                        (1744831011u32, 1usize, 40usize),
                        (1744970275u32, 2usize, 2usize),
                        (1744970275u32, 2usize, 17usize),
                        (1476674629u32, 2usize, 18usize),
                        (2097152u32, 2usize, 19usize),
                        (538688444u32, 2usize, 20usize),
                        (806984090u32, 2usize, 21usize),
                        (1744831011u32, 2usize, 40usize),
                        (1744970275u32, 17usize, 18usize),
                        (270392798u32, 17usize, 19usize),
                        (806984090u32, 17usize, 20usize),
                        (1075279736u32, 17usize, 21usize),
                        (1744831011u32, 17usize, 40usize),
                        (1744970275u32, 18usize, 18usize),
                        (2097152u32, 18usize, 19usize),
                        (538688444u32, 18usize, 20usize),
                        (806984090u32, 18usize, 21usize),
                        (1744831011u32, 18usize, 40usize),
                        (270392798u32, 19usize, 19usize),
                        (1077376888u32, 19usize, 20usize),
                        (1345672534u32, 19usize, 21usize),
                        (1744831011u32, 19usize, 40usize),
                        (806984090u32, 20usize, 20usize),
                        (1882263826u32, 20usize, 21usize),
                        (1744831011u32, 20usize, 40usize),
                        (1075279736u32, 21usize, 21usize),
                        (1744831011u32, 21usize, 40usize),
                        (1744830467u32, 179usize, 0usize),
                        (1744830467u32, 179usize, 1usize),
                        (1744830467u32, 179usize, 3usize),
                        (1744830467u32, 179usize, 4usize),
                        (1744830467u32, 179usize, 5usize),
                        (1744830467u32, 187usize, 2usize),
                        (1744830467u32, 195usize, 6usize),
                        (1744830467u32, 0usize, 23usize),
                        (1744830467u32, 1usize, 47usize),
                        (1744831011u32, 1usize, 48usize),
                        (1744830467u32, 2usize, 47usize),
                        (1744831011u32, 2usize, 48usize),
                        (1744830467u32, 17usize, 47usize),
                        (1744831011u32, 17usize, 48usize),
                        (1744830467u32, 18usize, 47usize),
                        (1744831011u32, 18usize, 48usize),
                        (1744830467u32, 19usize, 47usize),
                        (1744831011u32, 19usize, 48usize),
                        (1744830467u32, 20usize, 47usize),
                        (1744831011u32, 20usize, 48usize),
                        (1744830467u32, 21usize, 47usize),
                        (1744831011u32, 21usize, 48usize),
                        (1744830467u32, 179usize, 6usize),
                        (1744830467u32, 187usize, 5usize),
                        (1744830467u32, 219usize, 3usize),
                        (268435454u32, 1usize, 50usize),
                        (1744831011u32, 1usize, 56usize),
                        (1744830467u32, 2usize, 27usize),
                        (268435454u32, 2usize, 50usize),
                        (1744831011u32, 2usize, 56usize),
                        (1744830467u32, 6usize, 27usize),
                        (268435454u32, 17usize, 50usize),
                        (1744831011u32, 17usize, 56usize),
                        (268435454u32, 18usize, 50usize),
                        (1744831011u32, 18usize, 56usize),
                        (268435454u32, 19usize, 47usize),
                        (1744830467u32, 19usize, 55usize),
                        (544u32, 19usize, 56usize),
                        (268435454u32, 20usize, 49usize),
                        (1744830467u32, 20usize, 55usize),
                        (1744831011u32, 20usize, 56usize),
                        (268435454u32, 20usize, 58usize),
                        (268435454u32, 21usize, 49usize),
                        (1744830467u32, 21usize, 55usize),
                        (1744831011u32, 21usize, 56usize),
                        (268435454u32, 21usize, 58usize),
                        (1744830467u32, 181usize, 0usize),
                        (1744830467u32, 181usize, 3usize),
                        (1744830467u32, 181usize, 4usize),
                        (1744830467u32, 213usize, 5usize),
                        (1744830467u32, 221usize, 1usize),
                        (1744970275u32, 1usize, 1usize),
                        (1476674629u32, 1usize, 2usize),
                        (1744970275u32, 1usize, 17usize),
                        (1476674629u32, 1usize, 18usize),
                        (2097152u32, 1usize, 19usize),
                        (538688444u32, 1usize, 20usize),
                        (806984090u32, 1usize, 21usize),
                        (268435454u32, 1usize, 40usize),
                        (1744830467u32, 1usize, 41usize),
                        (1744831011u32, 1usize, 42usize),
                        (1744970275u32, 2usize, 2usize),
                        (1744970275u32, 2usize, 17usize),
                        (1476674629u32, 2usize, 18usize),
                        (2097152u32, 2usize, 19usize),
                        (538688444u32, 2usize, 20usize),
                        (806984090u32, 2usize, 21usize),
                        (268435454u32, 2usize, 40usize),
                        (1744830467u32, 2usize, 41usize),
                        (1744831011u32, 2usize, 42usize),
                        (1744970275u32, 17usize, 18usize),
                        (270392798u32, 17usize, 19usize),
                        (806984090u32, 17usize, 20usize),
                        (1075279736u32, 17usize, 21usize),
                        (268435454u32, 17usize, 40usize),
                        (1744830467u32, 17usize, 41usize),
                        (1744831011u32, 17usize, 42usize),
                        (1744970275u32, 18usize, 18usize),
                        (2097152u32, 18usize, 19usize),
                        (538688444u32, 18usize, 20usize),
                        (806984090u32, 18usize, 21usize),
                        (268435454u32, 18usize, 40usize),
                        (1744830467u32, 18usize, 41usize),
                        (1744831011u32, 18usize, 42usize),
                        (270392798u32, 19usize, 19usize),
                        (1077376888u32, 19usize, 20usize),
                        (1345672534u32, 19usize, 21usize),
                        (268435454u32, 19usize, 40usize),
                        (1744830467u32, 19usize, 41usize),
                        (1744831011u32, 19usize, 42usize),
                        (806984090u32, 20usize, 20usize),
                        (1882263826u32, 20usize, 21usize),
                        (268435454u32, 20usize, 40usize),
                        (1744830467u32, 20usize, 41usize),
                        (1744831011u32, 20usize, 42usize),
                        (1075279736u32, 21usize, 21usize),
                        (268435454u32, 21usize, 40usize),
                        (1744830467u32, 21usize, 41usize),
                        (1744831011u32, 21usize, 42usize),
                        (1744830467u32, 180usize, 0usize),
                        (1744830467u32, 180usize, 1usize),
                        (1744830467u32, 180usize, 3usize),
                        (1744830467u32, 180usize, 4usize),
                        (1744830467u32, 180usize, 5usize),
                        (1744830467u32, 188usize, 2usize),
                        (1744830467u32, 196usize, 6usize),
                        (1744830467u32, 0usize, 24usize),
                        (1744830467u32, 1usize, 49usize),
                        (1744831011u32, 1usize, 50usize),
                        (1744830467u32, 2usize, 49usize),
                        (1744831011u32, 2usize, 50usize),
                        (1744830467u32, 17usize, 49usize),
                        (1744831011u32, 17usize, 50usize),
                        (1744830467u32, 18usize, 49usize),
                        (1744831011u32, 18usize, 50usize),
                        (1744830467u32, 19usize, 49usize),
                        (1744831011u32, 19usize, 50usize),
                        (1744830467u32, 20usize, 49usize),
                        (1744831011u32, 20usize, 50usize),
                        (1744830467u32, 21usize, 49usize),
                        (1744831011u32, 21usize, 50usize),
                        (1744830467u32, 180usize, 6usize),
                        (1744830467u32, 188usize, 5usize),
                        (1744830467u32, 220usize, 3usize),
                        (268435454u32, 1usize, 47usize),
                        (268435454u32, 1usize, 56usize),
                        (1744830467u32, 1usize, 57usize),
                        (1744831011u32, 1usize, 58usize),
                        (1744830467u32, 2usize, 28usize),
                        (268435454u32, 2usize, 47usize),
                        (268435454u32, 2usize, 56usize),
                        (1744830467u32, 2usize, 57usize),
                        (1744831011u32, 2usize, 58usize),
                        (1744830467u32, 6usize, 28usize),
                        (268435454u32, 17usize, 47usize),
                        (268435454u32, 17usize, 56usize),
                        (1744830467u32, 17usize, 57usize),
                        (1744831011u32, 17usize, 58usize),
                        (268435454u32, 18usize, 47usize),
                        (268435454u32, 18usize, 56usize),
                        (1744830467u32, 18usize, 57usize),
                        (1744831011u32, 18usize, 58usize),
                        (268435454u32, 19usize, 48usize),
                        (1744831011u32, 19usize, 58usize),
                        (268435454u32, 20usize, 50usize),
                        (268435454u32, 20usize, 55usize),
                        (1744830467u32, 20usize, 57usize),
                        (1744831011u32, 20usize, 58usize),
                        (268435454u32, 21usize, 50usize),
                        (268435454u32, 21usize, 55usize),
                        (1744830467u32, 21usize, 57usize),
                        (1744831011u32, 21usize, 58usize),
                        (1744830467u32, 182usize, 0usize),
                        (1744830467u32, 182usize, 3usize),
                        (1744830467u32, 182usize, 4usize),
                        (1744830467u32, 214usize, 5usize),
                        (1744830467u32, 222usize, 1usize),
                        (1744970275u32, 1usize, 1usize),
                        (1476674629u32, 1usize, 2usize),
                        (1744970275u32, 1usize, 17usize),
                        (1476674629u32, 1usize, 18usize),
                        (2097152u32, 1usize, 19usize),
                        (538688444u32, 1usize, 20usize),
                        (806984090u32, 1usize, 21usize),
                        (268435454u32, 1usize, 41usize),
                        (1744830467u32, 1usize, 43usize),
                        (1744831011u32, 1usize, 44usize),
                        (1744970275u32, 2usize, 2usize),
                        (1744970275u32, 2usize, 17usize),
                        (1476674629u32, 2usize, 18usize),
                        (2097152u32, 2usize, 19usize),
                        (538688444u32, 2usize, 20usize),
                        (806984090u32, 2usize, 21usize),
                        (268435454u32, 2usize, 41usize),
                        (1744830467u32, 2usize, 43usize),
                        (1744831011u32, 2usize, 44usize),
                        (1744970275u32, 17usize, 18usize),
                        (270392798u32, 17usize, 19usize),
                        (806984090u32, 17usize, 20usize),
                        (1075279736u32, 17usize, 21usize),
                        (268435454u32, 17usize, 41usize),
                        (1744830467u32, 17usize, 43usize),
                        (1744831011u32, 17usize, 44usize),
                        (1744970275u32, 18usize, 18usize),
                        (2097152u32, 18usize, 19usize),
                        (538688444u32, 18usize, 20usize),
                        (806984090u32, 18usize, 21usize),
                        (268435454u32, 18usize, 41usize),
                        (1744830467u32, 18usize, 43usize),
                        (1744831011u32, 18usize, 44usize),
                        (270392798u32, 19usize, 19usize),
                        (1077376888u32, 19usize, 20usize),
                        (1345672534u32, 19usize, 21usize),
                        (268435454u32, 19usize, 41usize),
                        (1744830467u32, 19usize, 43usize),
                        (1744831011u32, 19usize, 44usize),
                        (806984090u32, 20usize, 20usize),
                        (1882263826u32, 20usize, 21usize),
                        (268435454u32, 20usize, 41usize),
                        (1744830467u32, 20usize, 43usize),
                        (1744831011u32, 20usize, 44usize),
                        (1075279736u32, 21usize, 21usize),
                        (268435454u32, 21usize, 41usize),
                        (1744830467u32, 21usize, 43usize),
                        (1744831011u32, 21usize, 44usize),
                        (1744830467u32, 183usize, 0usize),
                        (1744830467u32, 183usize, 1usize),
                        (1744830467u32, 183usize, 3usize),
                        (1744830467u32, 183usize, 4usize),
                        (1744830467u32, 183usize, 5usize),
                        (1744830467u32, 191usize, 2usize),
                        (1744830467u32, 199usize, 6usize),
                        (1744830467u32, 0usize, 25usize),
                        (1744830467u32, 1usize, 51usize),
                        (1744831011u32, 1usize, 52usize),
                        (1744830467u32, 2usize, 51usize),
                        (1744831011u32, 2usize, 52usize),
                        (1744830467u32, 17usize, 51usize),
                        (1744831011u32, 17usize, 52usize),
                        (1744830467u32, 18usize, 51usize),
                        (1744831011u32, 18usize, 52usize),
                        (1744830467u32, 19usize, 51usize),
                        (1744831011u32, 19usize, 52usize),
                        (1744830467u32, 20usize, 51usize),
                        (1744831011u32, 20usize, 52usize),
                        (1744830467u32, 21usize, 51usize),
                        (1744831011u32, 21usize, 52usize),
                        (1744830467u32, 183usize, 6usize),
                        (1744830467u32, 191usize, 5usize),
                        (1744830467u32, 223usize, 3usize),
                        (268435454u32, 1usize, 48usize),
                        (268435454u32, 1usize, 57usize),
                        (1744830467u32, 1usize, 59usize),
                        (1744831011u32, 1usize, 60usize),
                        (1744830467u32, 2usize, 29usize),
                        (268435454u32, 2usize, 48usize),
                        (268435454u32, 2usize, 57usize),
                        (1744830467u32, 2usize, 59usize),
                        (1744831011u32, 2usize, 60usize),
                        (1744830467u32, 6usize, 29usize),
                        (268435454u32, 17usize, 48usize),
                        (268435454u32, 17usize, 57usize),
                        (1744830467u32, 17usize, 59usize),
                        (1744831011u32, 17usize, 60usize),
                        (268435454u32, 18usize, 48usize),
                        (268435454u32, 18usize, 57usize),
                        (1744830467u32, 18usize, 59usize),
                        (1744831011u32, 18usize, 60usize),
                        (268435454u32, 19usize, 49usize),
                        (268435454u32, 19usize, 58usize),
                        (1744830467u32, 19usize, 59usize),
                        (1744831011u32, 19usize, 60usize),
                        (268435454u32, 20usize, 47usize),
                        (268435454u32, 20usize, 56usize),
                        (1744830467u32, 20usize, 59usize),
                        (1744831011u32, 20usize, 60usize),
                        (268435454u32, 21usize, 47usize),
                        (268435454u32, 21usize, 56usize),
                        (1744830467u32, 21usize, 59usize),
                        (1744831011u32, 21usize, 60usize),
                        (1744830467u32, 185usize, 0usize),
                        (1744830467u32, 185usize, 3usize),
                        (1744830467u32, 185usize, 4usize),
                        (1744830467u32, 217usize, 5usize),
                        (1744830467u32, 225usize, 1usize),
                        (1744970275u32, 1usize, 1usize),
                        (1476674629u32, 1usize, 2usize),
                        (1744970275u32, 1usize, 17usize),
                        (1476674629u32, 1usize, 18usize),
                        (2097152u32, 1usize, 19usize),
                        (538688444u32, 1usize, 20usize),
                        (806984090u32, 1usize, 21usize),
                        (268435454u32, 1usize, 42usize),
                        (1744830467u32, 1usize, 45usize),
                        (1744831011u32, 1usize, 46usize),
                        (1744970275u32, 2usize, 2usize),
                        (1744970275u32, 2usize, 17usize),
                        (1476674629u32, 2usize, 18usize),
                        (2097152u32, 2usize, 19usize),
                        (538688444u32, 2usize, 20usize),
                        (806984090u32, 2usize, 21usize),
                        (268435454u32, 2usize, 42usize),
                        (1744830467u32, 2usize, 45usize),
                        (1744831011u32, 2usize, 46usize),
                        (1744970275u32, 17usize, 18usize),
                        (270392798u32, 17usize, 19usize),
                        (806984090u32, 17usize, 20usize),
                        (1075279736u32, 17usize, 21usize),
                        (268435454u32, 17usize, 42usize),
                        (1744830467u32, 17usize, 45usize),
                        (1744831011u32, 17usize, 46usize),
                        (1744970275u32, 18usize, 18usize),
                        (2097152u32, 18usize, 19usize),
                        (538688444u32, 18usize, 20usize),
                        (806984090u32, 18usize, 21usize),
                        (268435454u32, 18usize, 42usize),
                        (1744830467u32, 18usize, 45usize),
                        (1744831011u32, 18usize, 46usize),
                        (270392798u32, 19usize, 19usize),
                        (1077376888u32, 19usize, 20usize),
                        (1345672534u32, 19usize, 21usize),
                        (268435454u32, 19usize, 42usize),
                        (1744830467u32, 19usize, 45usize),
                        (1744831011u32, 19usize, 46usize),
                        (806984090u32, 20usize, 20usize),
                        (1882263826u32, 20usize, 21usize),
                        (268435454u32, 20usize, 42usize),
                        (1744830467u32, 20usize, 45usize),
                        (1744831011u32, 20usize, 46usize),
                        (1075279736u32, 21usize, 21usize),
                        (268435454u32, 21usize, 42usize),
                        (1744830467u32, 21usize, 45usize),
                        (1744831011u32, 21usize, 46usize),
                        (1744830467u32, 184usize, 0usize),
                        (1744830467u32, 184usize, 1usize),
                        (1744830467u32, 184usize, 3usize),
                        (1744830467u32, 184usize, 4usize),
                        (1744830467u32, 184usize, 5usize),
                        (1744830467u32, 192usize, 2usize),
                        (1744830467u32, 200usize, 6usize),
                        (1744830467u32, 0usize, 26usize),
                        (1744830467u32, 1usize, 53usize),
                        (1744831011u32, 1usize, 54usize),
                        (1744830467u32, 2usize, 53usize),
                        (1744831011u32, 2usize, 54usize),
                        (1744830467u32, 17usize, 53usize),
                        (1744831011u32, 17usize, 54usize),
                        (1744830467u32, 18usize, 53usize),
                        (1744831011u32, 18usize, 54usize),
                        (1744830467u32, 19usize, 53usize),
                        (1744831011u32, 19usize, 54usize),
                        (1744830467u32, 20usize, 53usize),
                        (1744831011u32, 20usize, 54usize),
                        (1744830467u32, 21usize, 53usize),
                        (1744831011u32, 21usize, 54usize),
                        (1744830467u32, 184usize, 6usize),
                        (1744830467u32, 192usize, 5usize),
                        (1744830467u32, 224usize, 3usize),
                        (268435454u32, 1usize, 49usize),
                        (268435454u32, 1usize, 58usize),
                        (1744830467u32, 1usize, 61usize),
                        (1744831011u32, 1usize, 62usize),
                        (1744830467u32, 2usize, 30usize),
                        (268435454u32, 2usize, 49usize),
                        (268435454u32, 2usize, 58usize),
                        (1744830467u32, 2usize, 61usize),
                        (1744831011u32, 2usize, 62usize),
                        (1744830467u32, 6usize, 30usize),
                        (268435454u32, 17usize, 49usize),
                        (268435454u32, 17usize, 58usize),
                        (1744830467u32, 17usize, 61usize),
                        (1744831011u32, 17usize, 62usize),
                        (268435454u32, 18usize, 49usize),
                        (268435454u32, 18usize, 58usize),
                        (1744830467u32, 18usize, 61usize),
                        (1744831011u32, 18usize, 62usize),
                        (268435454u32, 19usize, 50usize),
                        (268435454u32, 19usize, 55usize),
                        (1744830467u32, 19usize, 61usize),
                        (1744831011u32, 19usize, 62usize),
                        (268435454u32, 20usize, 48usize),
                        (268435454u32, 20usize, 57usize),
                        (1744830467u32, 20usize, 61usize),
                        (1744831011u32, 20usize, 62usize),
                        (268435454u32, 21usize, 48usize),
                        (268435454u32, 21usize, 57usize),
                        (1744830467u32, 21usize, 61usize),
                        (1744831011u32, 21usize, 62usize),
                        (1744830467u32, 186usize, 0usize),
                        (1744830467u32, 186usize, 3usize),
                        (1744830467u32, 186usize, 4usize),
                        (1744830467u32, 218usize, 5usize),
                        (1744830467u32, 226usize, 1usize),
                        (1744970275u32, 1usize, 1usize),
                        (671787691u32, 1usize, 17usize),
                        (538688444u32, 1usize, 18usize),
                        (135196399u32, 1usize, 19usize),
                        (1880166674u32, 1usize, 20usize),
                        (671787691u32, 1usize, 21usize),
                        (1744831011u32, 1usize, 64usize),
                        (940083337u32, 17usize, 17usize),
                        (1747067427u32, 17usize, 18usize),
                        (1343575382u32, 17usize, 19usize),
                        (1075279736u32, 17usize, 20usize),
                        (1880166674u32, 17usize, 21usize),
                        (1744831011u32, 17usize, 64usize),
                        (806984090u32, 18usize, 18usize),
                        (1210476135u32, 18usize, 19usize),
                        (942180489u32, 18usize, 20usize),
                        (1747067427u32, 18usize, 21usize),
                        (1744831011u32, 18usize, 64usize),
                        (403492045u32, 19usize, 19usize),
                        (538688444u32, 19usize, 20usize),
                        (1343575382u32, 19usize, 21usize),
                        (1744831011u32, 19usize, 64usize),
                        (135196399u32, 20usize, 20usize),
                        (1075279736u32, 20usize, 21usize),
                        (1744831011u32, 20usize, 64usize),
                        (940083337u32, 21usize, 21usize),
                        (1744831011u32, 21usize, 64usize),
                        (1744830467u32, 181usize, 0usize),
                        (1744830467u32, 187usize, 3usize),
                        (1744830467u32, 187usize, 4usize),
                        (1744830467u32, 187usize, 5usize),
                        (1744830467u32, 187usize, 6usize),
                        (1744830467u32, 195usize, 1usize),
                        (1744830467u32, 211usize, 2usize),
                        (1744830467u32, 1usize, 71usize),
                        (1744831011u32, 1usize, 72usize),
                        (1744830467u32, 2usize, 27usize),
                        (1744830467u32, 6usize, 27usize),
                        (1744830467u32, 17usize, 71usize),
                        (1744831011u32, 17usize, 72usize),
                        (1744830467u32, 18usize, 71usize),
                        (1744831011u32, 18usize, 72usize),
                        (1744830467u32, 19usize, 71usize),
                        (1744831011u32, 19usize, 72usize),
                        (1744830467u32, 20usize, 71usize),
                        (1744831011u32, 20usize, 72usize),
                        (1744830467u32, 21usize, 71usize),
                        (1744831011u32, 21usize, 72usize),
                        (1744830467u32, 187usize, 0usize),
                        (1744830467u32, 195usize, 5usize),
                        (1744830467u32, 219usize, 3usize),
                        (1744830467u32, 0usize, 27usize),
                        (1744830467u32, 1usize, 27usize),
                        (268435454u32, 1usize, 74usize),
                        (1744831011u32, 1usize, 80usize),
                        (1744830467u32, 5usize, 27usize),
                        (268435454u32, 17usize, 72usize),
                        (1744830467u32, 17usize, 79usize),
                        (1744831011u32, 17usize, 80usize),
                        (268435454u32, 17usize, 81usize),
                        (268435454u32, 18usize, 72usize),
                        (1744830467u32, 18usize, 79usize),
                        (1744831011u32, 18usize, 80usize),
                        (268435454u32, 18usize, 81usize),
                        (268435454u32, 19usize, 74usize),
                        (1744831011u32, 19usize, 80usize),
                        (268435454u32, 20usize, 71usize),
                        (1744830467u32, 20usize, 79usize),
                        (544u32, 20usize, 80usize),
                        (268435454u32, 21usize, 73usize),
                        (1744830467u32, 21usize, 79usize),
                        (1744831011u32, 21usize, 80usize),
                        (268435454u32, 21usize, 82usize),
                        (1744830467u32, 189usize, 3usize),
                        (1744830467u32, 189usize, 4usize),
                        (1744830467u32, 189usize, 6usize),
                        (1744830467u32, 213usize, 2usize),
                        (1744970275u32, 1usize, 1usize),
                        (671787691u32, 1usize, 17usize),
                        (538688444u32, 1usize, 18usize),
                        (135196399u32, 1usize, 19usize),
                        (1880166674u32, 1usize, 20usize),
                        (671787691u32, 1usize, 21usize),
                        (268435454u32, 1usize, 64usize),
                        (1744830467u32, 1usize, 65usize),
                        (1744831011u32, 1usize, 66usize),
                        (940083337u32, 17usize, 17usize),
                        (1747067427u32, 17usize, 18usize),
                        (1343575382u32, 17usize, 19usize),
                        (1075279736u32, 17usize, 20usize),
                        (1880166674u32, 17usize, 21usize),
                        (268435454u32, 17usize, 64usize),
                        (1744830467u32, 17usize, 65usize),
                        (1744831011u32, 17usize, 66usize),
                        (806984090u32, 18usize, 18usize),
                        (1210476135u32, 18usize, 19usize),
                        (942180489u32, 18usize, 20usize),
                        (1747067427u32, 18usize, 21usize),
                        (268435454u32, 18usize, 64usize),
                        (1744830467u32, 18usize, 65usize),
                        (1744831011u32, 18usize, 66usize),
                        (403492045u32, 19usize, 19usize),
                        (538688444u32, 19usize, 20usize),
                        (1343575382u32, 19usize, 21usize),
                        (268435454u32, 19usize, 64usize),
                        (1744830467u32, 19usize, 65usize),
                        (1744831011u32, 19usize, 66usize),
                        (135196399u32, 20usize, 20usize),
                        (1075279736u32, 20usize, 21usize),
                        (268435454u32, 20usize, 64usize),
                        (1744830467u32, 20usize, 65usize),
                        (1744831011u32, 20usize, 66usize),
                        (940083337u32, 21usize, 21usize),
                        (268435454u32, 21usize, 64usize),
                        (1744830467u32, 21usize, 65usize),
                        (1744831011u32, 21usize, 66usize),
                        (1744830467u32, 182usize, 0usize),
                        (1744830467u32, 188usize, 3usize),
                        (1744830467u32, 188usize, 4usize),
                        (1744830467u32, 188usize, 5usize),
                        (1744830467u32, 188usize, 6usize),
                        (1744830467u32, 196usize, 1usize),
                        (1744830467u32, 212usize, 2usize),
                        (1744830467u32, 1usize, 73usize),
                        (1744831011u32, 1usize, 74usize),
                        (1744830467u32, 2usize, 28usize),
                        (1744830467u32, 6usize, 28usize),
                        (1744830467u32, 17usize, 73usize),
                        (1744831011u32, 17usize, 74usize),
                        (1744830467u32, 18usize, 73usize),
                        (1744831011u32, 18usize, 74usize),
                        (1744830467u32, 19usize, 73usize),
                        (1744831011u32, 19usize, 74usize),
                        (1744830467u32, 20usize, 73usize),
                        (1744831011u32, 20usize, 74usize),
                        (1744830467u32, 21usize, 73usize),
                        (1744831011u32, 21usize, 74usize),
                        (1744830467u32, 188usize, 0usize),
                        (1744830467u32, 196usize, 5usize),
                        (1744830467u32, 220usize, 3usize),
                        (1744830467u32, 0usize, 28usize),
                        (1744830467u32, 1usize, 28usize),
                        (268435454u32, 1usize, 71usize),
                        (268435454u32, 1usize, 80usize),
                        (1744830467u32, 1usize, 81usize),
                        (1744831011u32, 1usize, 82usize),
                        (1744830467u32, 5usize, 28usize),
                        (268435454u32, 17usize, 73usize),
                        (1744830467u32, 17usize, 81usize),
                        (544u32, 17usize, 82usize),
                        (268435454u32, 18usize, 73usize),
                        (1744830467u32, 18usize, 81usize),
                        (544u32, 18usize, 82usize),
                        (268435454u32, 19usize, 71usize),
                        (268435454u32, 19usize, 80usize),
                        (1744830467u32, 19usize, 81usize),
                        (1744831011u32, 19usize, 82usize),
                        (268435454u32, 20usize, 72usize),
                        (1744831011u32, 20usize, 82usize),
                        (268435454u32, 21usize, 74usize),
                        (268435454u32, 21usize, 79usize),
                        (1744830467u32, 21usize, 81usize),
                        (1744831011u32, 21usize, 82usize),
                        (1744830467u32, 190usize, 3usize),
                        (1744830467u32, 190usize, 4usize),
                        (1744830467u32, 190usize, 6usize),
                        (1744830467u32, 214usize, 2usize),
                        (1744970275u32, 1usize, 1usize),
                        (671787691u32, 1usize, 17usize),
                        (538688444u32, 1usize, 18usize),
                        (135196399u32, 1usize, 19usize),
                        (1880166674u32, 1usize, 20usize),
                        (671787691u32, 1usize, 21usize),
                        (268435454u32, 1usize, 65usize),
                        (1744830467u32, 1usize, 67usize),
                        (1744831011u32, 1usize, 68usize),
                        (940083337u32, 17usize, 17usize),
                        (1747067427u32, 17usize, 18usize),
                        (1343575382u32, 17usize, 19usize),
                        (1075279736u32, 17usize, 20usize),
                        (1880166674u32, 17usize, 21usize),
                        (268435454u32, 17usize, 65usize),
                        (1744830467u32, 17usize, 67usize),
                        (1744831011u32, 17usize, 68usize),
                        (806984090u32, 18usize, 18usize),
                        (1210476135u32, 18usize, 19usize),
                        (942180489u32, 18usize, 20usize),
                        (1747067427u32, 18usize, 21usize),
                        (268435454u32, 18usize, 65usize),
                        (1744830467u32, 18usize, 67usize),
                        (1744831011u32, 18usize, 68usize),
                        (403492045u32, 19usize, 19usize),
                        (538688444u32, 19usize, 20usize),
                        (1343575382u32, 19usize, 21usize),
                        (268435454u32, 19usize, 65usize),
                        (1744830467u32, 19usize, 67usize),
                        (1744831011u32, 19usize, 68usize),
                        (135196399u32, 20usize, 20usize),
                        (1075279736u32, 20usize, 21usize),
                        (268435454u32, 20usize, 65usize),
                        (1744830467u32, 20usize, 67usize),
                        (1744831011u32, 20usize, 68usize),
                        (940083337u32, 21usize, 21usize),
                        (268435454u32, 21usize, 65usize),
                        (1744830467u32, 21usize, 67usize),
                        (1744831011u32, 21usize, 68usize),
                        (1744830467u32, 185usize, 0usize),
                        (1744830467u32, 191usize, 3usize),
                        (1744830467u32, 191usize, 4usize),
                        (1744830467u32, 191usize, 5usize),
                        (1744830467u32, 191usize, 6usize),
                        (1744830467u32, 199usize, 1usize),
                        (1744830467u32, 215usize, 2usize),
                        (1744830467u32, 1usize, 75usize),
                        (1744831011u32, 1usize, 76usize),
                        (1744830467u32, 2usize, 29usize),
                        (1744830467u32, 6usize, 29usize),
                        (1744830467u32, 17usize, 75usize),
                        (1744831011u32, 17usize, 76usize),
                        (1744830467u32, 18usize, 75usize),
                        (1744831011u32, 18usize, 76usize),
                        (1744830467u32, 19usize, 75usize),
                        (1744831011u32, 19usize, 76usize),
                        (1744830467u32, 20usize, 75usize),
                        (1744831011u32, 20usize, 76usize),
                        (1744830467u32, 21usize, 75usize),
                        (1744831011u32, 21usize, 76usize),
                        (1744830467u32, 191usize, 0usize),
                        (1744830467u32, 199usize, 5usize),
                        (1744830467u32, 223usize, 3usize),
                        (1744830467u32, 0usize, 29usize),
                        (1744830467u32, 1usize, 29usize),
                        (268435454u32, 1usize, 72usize),
                        (268435454u32, 1usize, 81usize),
                        (1744830467u32, 1usize, 83usize),
                        (1744831011u32, 1usize, 84usize),
                        (1744830467u32, 5usize, 29usize),
                        (268435454u32, 17usize, 74usize),
                        (268435454u32, 17usize, 79usize),
                        (1744830467u32, 17usize, 83usize),
                        (1744831011u32, 17usize, 84usize),
                        (268435454u32, 18usize, 74usize),
                        (268435454u32, 18usize, 79usize),
                        (1744830467u32, 18usize, 83usize),
                        (1744831011u32, 18usize, 84usize),
                        (268435454u32, 19usize, 72usize),
                        (268435454u32, 19usize, 81usize),
                        (1744830467u32, 19usize, 83usize),
                        (1744831011u32, 19usize, 84usize),
                        (268435454u32, 20usize, 73usize),
                        (268435454u32, 20usize, 82usize),
                        (1744830467u32, 20usize, 83usize),
                        (1744831011u32, 20usize, 84usize),
                        (268435454u32, 21usize, 71usize),
                        (268435454u32, 21usize, 80usize),
                        (1744830467u32, 21usize, 83usize),
                        (1744831011u32, 21usize, 84usize),
                        (1744830467u32, 193usize, 3usize),
                        (1744830467u32, 193usize, 4usize),
                        (1744830467u32, 193usize, 6usize),
                        (1744830467u32, 217usize, 2usize),
                        (1744970275u32, 1usize, 1usize),
                        (671787691u32, 1usize, 17usize),
                        (538688444u32, 1usize, 18usize),
                        (135196399u32, 1usize, 19usize),
                        (1880166674u32, 1usize, 20usize),
                        (671787691u32, 1usize, 21usize),
                        (268435454u32, 1usize, 66usize),
                        (1744830467u32, 1usize, 69usize),
                        (1744831011u32, 1usize, 70usize),
                        (940083337u32, 17usize, 17usize),
                        (1747067427u32, 17usize, 18usize),
                        (1343575382u32, 17usize, 19usize),
                        (1075279736u32, 17usize, 20usize),
                        (1880166674u32, 17usize, 21usize),
                        (268435454u32, 17usize, 66usize),
                        (1744830467u32, 17usize, 69usize),
                        (1744831011u32, 17usize, 70usize),
                        (806984090u32, 18usize, 18usize),
                        (1210476135u32, 18usize, 19usize),
                        (942180489u32, 18usize, 20usize),
                        (1747067427u32, 18usize, 21usize),
                        (268435454u32, 18usize, 66usize),
                        (1744830467u32, 18usize, 69usize),
                        (1744831011u32, 18usize, 70usize),
                        (403492045u32, 19usize, 19usize),
                        (538688444u32, 19usize, 20usize),
                        (1343575382u32, 19usize, 21usize),
                        (268435454u32, 19usize, 66usize),
                        (1744830467u32, 19usize, 69usize),
                        (1744831011u32, 19usize, 70usize),
                        (135196399u32, 20usize, 20usize),
                        (1075279736u32, 20usize, 21usize),
                        (268435454u32, 20usize, 66usize),
                        (1744830467u32, 20usize, 69usize),
                        (1744831011u32, 20usize, 70usize),
                        (940083337u32, 21usize, 21usize),
                        (268435454u32, 21usize, 66usize),
                        (1744830467u32, 21usize, 69usize),
                        (1744831011u32, 21usize, 70usize),
                        (1744830467u32, 186usize, 0usize),
                        (1744830467u32, 192usize, 3usize),
                        (1744830467u32, 192usize, 4usize),
                        (1744830467u32, 192usize, 5usize),
                        (1744830467u32, 192usize, 6usize),
                        (1744830467u32, 200usize, 1usize),
                        (1744830467u32, 216usize, 2usize),
                        (1744830467u32, 1usize, 77usize),
                        (1744831011u32, 1usize, 78usize),
                        (1744830467u32, 2usize, 30usize),
                        (1744830467u32, 6usize, 30usize),
                        (1744830467u32, 17usize, 77usize),
                        (1744831011u32, 17usize, 78usize),
                        (1744830467u32, 18usize, 77usize),
                        (1744831011u32, 18usize, 78usize),
                        (1744830467u32, 19usize, 77usize),
                        (1744831011u32, 19usize, 78usize),
                        (1744830467u32, 20usize, 77usize),
                        (1744831011u32, 20usize, 78usize),
                        (1744830467u32, 21usize, 77usize),
                        (1744831011u32, 21usize, 78usize),
                        (1744830467u32, 192usize, 0usize),
                        (1744830467u32, 200usize, 5usize),
                        (1744830467u32, 224usize, 3usize),
                        (1744830467u32, 0usize, 30usize),
                        (1744830467u32, 1usize, 30usize),
                        (268435454u32, 1usize, 73usize),
                        (268435454u32, 1usize, 82usize),
                        (1744830467u32, 1usize, 85usize),
                        (1744831011u32, 1usize, 86usize),
                        (1744830467u32, 5usize, 30usize),
                        (268435454u32, 17usize, 71usize),
                        (268435454u32, 17usize, 80usize),
                        (1744830467u32, 17usize, 85usize),
                        (1744831011u32, 17usize, 86usize),
                        (268435454u32, 18usize, 71usize),
                        (268435454u32, 18usize, 80usize),
                        (1744830467u32, 18usize, 85usize),
                        (1744831011u32, 18usize, 86usize),
                        (268435454u32, 19usize, 73usize),
                        (268435454u32, 19usize, 82usize),
                        (1744830467u32, 19usize, 85usize),
                        (1744831011u32, 19usize, 86usize),
                        (268435454u32, 20usize, 74usize),
                        (268435454u32, 20usize, 79usize),
                        (1744830467u32, 20usize, 85usize),
                        (1744831011u32, 20usize, 86usize),
                        (268435454u32, 21usize, 72usize),
                        (268435454u32, 21usize, 81usize),
                        (1744830467u32, 21usize, 85usize),
                        (1744831011u32, 21usize, 86usize),
                        (1744830467u32, 194usize, 3usize),
                        (1744830467u32, 194usize, 4usize),
                        (1744830467u32, 194usize, 6usize),
                        (1744830467u32, 218usize, 2usize),
                        (1744830467u32, 0usize, 27usize),
                        (1744970275u32, 2usize, 2usize),
                        (940083337u32, 2usize, 17usize),
                        (1075279736u32, 2usize, 18usize),
                        (806984090u32, 2usize, 19usize),
                        (1343575382u32, 2usize, 20usize),
                        (1880166674u32, 2usize, 21usize),
                        (1744831011u32, 2usize, 88usize),
                        (1208378983u32, 17usize, 17usize),
                        (538688444u32, 17usize, 18usize),
                        (270392798u32, 17usize, 19usize),
                        (806984090u32, 17usize, 20usize),
                        (1343575382u32, 17usize, 21usize),
                        (1744831011u32, 17usize, 88usize),
                        (1343575382u32, 18usize, 18usize),
                        (405589197u32, 18usize, 19usize),
                        (942180489u32, 18usize, 20usize),
                        (1478771781u32, 18usize, 21usize),
                        (1744831011u32, 18usize, 88usize),
                        (1075279736u32, 19usize, 19usize),
                        (673884843u32, 19usize, 20usize),
                        (1210476135u32, 19usize, 21usize),
                        (1744831011u32, 19usize, 88usize),
                        (1611871028u32, 20usize, 20usize),
                        (1747067427u32, 20usize, 21usize),
                        (1744831011u32, 20usize, 88usize),
                        (135196399u32, 21usize, 21usize),
                        (1744831011u32, 21usize, 88usize),
                        (1744830467u32, 179usize, 1usize),
                        (1744830467u32, 179usize, 5usize),
                        (1744830467u32, 179usize, 6usize),
                        (1744830467u32, 195usize, 3usize),
                        (1744830467u32, 195usize, 4usize),
                        (1744830467u32, 203usize, 2usize),
                        (1744830467u32, 1usize, 27usize),
                        (1744830467u32, 2usize, 95usize),
                        (1744831011u32, 2usize, 96usize),
                        (1744830467u32, 5usize, 27usize),
                        (1744830467u32, 17usize, 95usize),
                        (1744831011u32, 17usize, 96usize),
                        (1744830467u32, 18usize, 95usize),
                        (1744831011u32, 18usize, 96usize),
                        (1744830467u32, 19usize, 95usize),
                        (1744831011u32, 19usize, 96usize),
                        (1744830467u32, 20usize, 95usize),
                        (1744831011u32, 20usize, 96usize),
                        (1744830467u32, 21usize, 95usize),
                        (1744831011u32, 21usize, 96usize),
                        (1744830467u32, 195usize, 0usize),
                        (1744830467u32, 211usize, 6usize),
                        (1744830467u32, 219usize, 3usize),
                        (1744830467u32, 0usize, 31usize),
                        (1744830467u32, 2usize, 31usize),
                        (268435454u32, 2usize, 98usize),
                        (1744831011u32, 2usize, 104usize),
                        (1744830467u32, 6usize, 31usize),
                        (268435454u32, 17usize, 98usize),
                        (1744831011u32, 17usize, 104usize),
                        (268435454u32, 18usize, 98usize),
                        (1744831011u32, 18usize, 104usize),
                        (268435454u32, 19usize, 96usize),
                        (1744830467u32, 19usize, 103usize),
                        (1744831011u32, 19usize, 104usize),
                        (268435454u32, 19usize, 105usize),
                        (268435454u32, 20usize, 97usize),
                        (1744830467u32, 20usize, 103usize),
                        (1744831011u32, 20usize, 104usize),
                        (268435454u32, 20usize, 106usize),
                        (268435454u32, 21usize, 96usize),
                        (1744830467u32, 21usize, 103usize),
                        (1744831011u32, 21usize, 104usize),
                        (268435454u32, 21usize, 105usize),
                        (1744830467u32, 181usize, 1usize),
                        (1744830467u32, 181usize, 5usize),
                        (1744830467u32, 197usize, 3usize),
                        (1744830467u32, 197usize, 4usize),
                        (1744830467u32, 0usize, 28usize),
                        (1744970275u32, 2usize, 2usize),
                        (940083337u32, 2usize, 17usize),
                        (1075279736u32, 2usize, 18usize),
                        (806984090u32, 2usize, 19usize),
                        (1343575382u32, 2usize, 20usize),
                        (1880166674u32, 2usize, 21usize),
                        (268435454u32, 2usize, 88usize),
                        (1744830467u32, 2usize, 89usize),
                        (1744831011u32, 2usize, 90usize),
                        (1208378983u32, 17usize, 17usize),
                        (538688444u32, 17usize, 18usize),
                        (270392798u32, 17usize, 19usize),
                        (806984090u32, 17usize, 20usize),
                        (1343575382u32, 17usize, 21usize),
                        (268435454u32, 17usize, 88usize),
                        (1744830467u32, 17usize, 89usize),
                        (1744831011u32, 17usize, 90usize),
                        (1343575382u32, 18usize, 18usize),
                        (405589197u32, 18usize, 19usize),
                        (942180489u32, 18usize, 20usize),
                        (1478771781u32, 18usize, 21usize),
                        (268435454u32, 18usize, 88usize),
                        (1744830467u32, 18usize, 89usize),
                        (1744831011u32, 18usize, 90usize),
                        (1075279736u32, 19usize, 19usize),
                        (673884843u32, 19usize, 20usize),
                        (1210476135u32, 19usize, 21usize),
                        (268435454u32, 19usize, 88usize),
                        (1744830467u32, 19usize, 89usize),
                        (1744831011u32, 19usize, 90usize),
                        (1611871028u32, 20usize, 20usize),
                        (1747067427u32, 20usize, 21usize),
                        (268435454u32, 20usize, 88usize),
                        (1744830467u32, 20usize, 89usize),
                        (1744831011u32, 20usize, 90usize),
                        (135196399u32, 21usize, 21usize),
                        (268435454u32, 21usize, 88usize),
                        (1744830467u32, 21usize, 89usize),
                        (1744831011u32, 21usize, 90usize),
                        (1744830467u32, 180usize, 1usize),
                        (1744830467u32, 180usize, 5usize),
                        (1744830467u32, 180usize, 6usize),
                        (1744830467u32, 196usize, 3usize),
                        (1744830467u32, 196usize, 4usize),
                        (1744830467u32, 204usize, 2usize),
                        (1744830467u32, 1usize, 28usize),
                        (1744830467u32, 2usize, 97usize),
                        (1744831011u32, 2usize, 98usize),
                        (1744830467u32, 5usize, 28usize),
                        (1744830467u32, 17usize, 97usize),
                        (1744831011u32, 17usize, 98usize),
                        (1744830467u32, 18usize, 97usize),
                        (1744831011u32, 18usize, 98usize),
                        (1744830467u32, 19usize, 97usize),
                        (1744831011u32, 19usize, 98usize),
                        (1744830467u32, 20usize, 97usize),
                        (1744831011u32, 20usize, 98usize),
                        (1744830467u32, 21usize, 97usize),
                        (1744831011u32, 21usize, 98usize),
                        (1744830467u32, 196usize, 0usize),
                        (1744830467u32, 212usize, 6usize),
                        (1744830467u32, 220usize, 3usize),
                        (1744830467u32, 0usize, 32usize),
                        (1744830467u32, 2usize, 32usize),
                        (268435454u32, 2usize, 95usize),
                        (268435454u32, 2usize, 104usize),
                        (1744830467u32, 2usize, 105usize),
                        (1744831011u32, 2usize, 106usize),
                        (1744830467u32, 6usize, 32usize),
                        (268435454u32, 17usize, 95usize),
                        (268435454u32, 17usize, 104usize),
                        (1744830467u32, 17usize, 105usize),
                        (1744831011u32, 17usize, 106usize),
                        (268435454u32, 18usize, 95usize),
                        (268435454u32, 18usize, 104usize),
                        (1744830467u32, 18usize, 105usize),
                        (1744831011u32, 18usize, 106usize),
                        (268435454u32, 19usize, 97usize),
                        (1744830467u32, 19usize, 105usize),
                        (544u32, 19usize, 106usize),
                        (268435454u32, 20usize, 98usize),
                        (268435454u32, 20usize, 103usize),
                        (1744830467u32, 20usize, 105usize),
                        (1744831011u32, 20usize, 106usize),
                        (268435454u32, 21usize, 97usize),
                        (1744830467u32, 21usize, 105usize),
                        (544u32, 21usize, 106usize),
                        (1744830467u32, 182usize, 1usize),
                        (1744830467u32, 182usize, 5usize),
                        (1744830467u32, 198usize, 3usize),
                        (1744830467u32, 198usize, 4usize),
                        (1744830467u32, 0usize, 29usize),
                        (1744970275u32, 2usize, 2usize),
                        (940083337u32, 2usize, 17usize),
                        (1075279736u32, 2usize, 18usize),
                        (806984090u32, 2usize, 19usize),
                        (1343575382u32, 2usize, 20usize),
                        (1880166674u32, 2usize, 21usize),
                        (268435454u32, 2usize, 89usize),
                        (1744830467u32, 2usize, 91usize),
                        (1744831011u32, 2usize, 92usize),
                        (1208378983u32, 17usize, 17usize),
                        (538688444u32, 17usize, 18usize),
                        (270392798u32, 17usize, 19usize),
                        (806984090u32, 17usize, 20usize),
                        (1343575382u32, 17usize, 21usize),
                        (268435454u32, 17usize, 89usize),
                        (1744830467u32, 17usize, 91usize),
                        (1744831011u32, 17usize, 92usize),
                        (1343575382u32, 18usize, 18usize),
                        (405589197u32, 18usize, 19usize),
                        (942180489u32, 18usize, 20usize),
                        (1478771781u32, 18usize, 21usize),
                        (268435454u32, 18usize, 89usize),
                        (1744830467u32, 18usize, 91usize),
                        (1744831011u32, 18usize, 92usize),
                        (1075279736u32, 19usize, 19usize),
                        (673884843u32, 19usize, 20usize),
                        (1210476135u32, 19usize, 21usize),
                        (268435454u32, 19usize, 89usize),
                        (1744830467u32, 19usize, 91usize),
                        (1744831011u32, 19usize, 92usize),
                        (1611871028u32, 20usize, 20usize),
                        (1747067427u32, 20usize, 21usize),
                        (268435454u32, 20usize, 89usize),
                        (1744830467u32, 20usize, 91usize),
                        (1744831011u32, 20usize, 92usize),
                        (135196399u32, 21usize, 21usize),
                        (268435454u32, 21usize, 89usize),
                        (1744830467u32, 21usize, 91usize),
                        (1744831011u32, 21usize, 92usize),
                        (1744830467u32, 183usize, 1usize),
                        (1744830467u32, 183usize, 5usize),
                        (1744830467u32, 183usize, 6usize),
                        (1744830467u32, 199usize, 3usize),
                        (1744830467u32, 199usize, 4usize),
                        (1744830467u32, 207usize, 2usize),
                        (1744830467u32, 1usize, 29usize),
                        (1744830467u32, 2usize, 99usize),
                        (1744831011u32, 2usize, 100usize),
                        (1744830467u32, 5usize, 29usize),
                        (1744830467u32, 17usize, 99usize),
                        (1744831011u32, 17usize, 100usize),
                        (1744830467u32, 18usize, 99usize),
                        (1744831011u32, 18usize, 100usize),
                        (1744830467u32, 19usize, 99usize),
                        (1744831011u32, 19usize, 100usize),
                        (1744830467u32, 20usize, 99usize),
                        (1744831011u32, 20usize, 100usize),
                        (1744830467u32, 21usize, 99usize),
                        (1744831011u32, 21usize, 100usize),
                        (1744830467u32, 199usize, 0usize),
                        (1744830467u32, 215usize, 6usize),
                        (1744830467u32, 223usize, 3usize),
                        (1744830467u32, 0usize, 33usize),
                        (1744830467u32, 2usize, 33usize),
                        (268435454u32, 2usize, 96usize),
                        (268435454u32, 2usize, 105usize),
                        (1744830467u32, 2usize, 107usize),
                        (1744831011u32, 2usize, 108usize),
                        (1744830467u32, 6usize, 33usize),
                        (268435454u32, 17usize, 96usize),
                        (268435454u32, 17usize, 105usize),
                        (1744830467u32, 17usize, 107usize),
                        (1744831011u32, 17usize, 108usize),
                        (268435454u32, 18usize, 96usize),
                        (268435454u32, 18usize, 105usize),
                        (1744830467u32, 18usize, 107usize),
                        (1744831011u32, 18usize, 108usize),
                        (268435454u32, 19usize, 98usize),
                        (268435454u32, 19usize, 103usize),
                        (1744830467u32, 19usize, 107usize),
                        (1744831011u32, 19usize, 108usize),
                        (268435454u32, 20usize, 95usize),
                        (268435454u32, 20usize, 104usize),
                        (1744830467u32, 20usize, 107usize),
                        (1744831011u32, 20usize, 108usize),
                        (268435454u32, 21usize, 98usize),
                        (268435454u32, 21usize, 103usize),
                        (1744830467u32, 21usize, 107usize),
                        (1744831011u32, 21usize, 108usize),
                        (1744830467u32, 185usize, 1usize),
                        (1744830467u32, 185usize, 5usize),
                        (1744830467u32, 201usize, 3usize),
                        (1744830467u32, 201usize, 4usize),
                        (1744830467u32, 0usize, 30usize),
                        (1744970275u32, 2usize, 2usize),
                        (940083337u32, 2usize, 17usize),
                        (1075279736u32, 2usize, 18usize),
                        (806984090u32, 2usize, 19usize),
                        (1343575382u32, 2usize, 20usize),
                        (1880166674u32, 2usize, 21usize),
                        (268435454u32, 2usize, 90usize),
                        (1744830467u32, 2usize, 93usize),
                        (1744831011u32, 2usize, 94usize),
                        (1208378983u32, 17usize, 17usize),
                        (538688444u32, 17usize, 18usize),
                        (270392798u32, 17usize, 19usize),
                        (806984090u32, 17usize, 20usize),
                        (1343575382u32, 17usize, 21usize),
                        (268435454u32, 17usize, 90usize),
                        (1744830467u32, 17usize, 93usize),
                        (1744831011u32, 17usize, 94usize),
                        (1343575382u32, 18usize, 18usize),
                        (405589197u32, 18usize, 19usize),
                        (942180489u32, 18usize, 20usize),
                        (1478771781u32, 18usize, 21usize),
                        (268435454u32, 18usize, 90usize),
                        (1744830467u32, 18usize, 93usize),
                        (1744831011u32, 18usize, 94usize),
                        (1075279736u32, 19usize, 19usize),
                        (673884843u32, 19usize, 20usize),
                        (1210476135u32, 19usize, 21usize),
                        (268435454u32, 19usize, 90usize),
                        (1744830467u32, 19usize, 93usize),
                        (1744831011u32, 19usize, 94usize),
                        (1611871028u32, 20usize, 20usize),
                        (1747067427u32, 20usize, 21usize),
                        (268435454u32, 20usize, 90usize),
                        (1744830467u32, 20usize, 93usize),
                        (1744831011u32, 20usize, 94usize),
                        (135196399u32, 21usize, 21usize),
                        (268435454u32, 21usize, 90usize),
                        (1744830467u32, 21usize, 93usize),
                        (1744831011u32, 21usize, 94usize),
                        (1744830467u32, 184usize, 1usize),
                        (1744830467u32, 184usize, 5usize),
                        (1744830467u32, 184usize, 6usize),
                        (1744830467u32, 200usize, 3usize),
                        (1744830467u32, 200usize, 4usize),
                        (1744830467u32, 208usize, 2usize),
                        (1744830467u32, 1usize, 30usize),
                        (1744830467u32, 2usize, 101usize),
                        (1744831011u32, 2usize, 102usize),
                        (1744830467u32, 5usize, 30usize),
                        (1744830467u32, 17usize, 101usize),
                        (1744831011u32, 17usize, 102usize),
                        (1744830467u32, 18usize, 101usize),
                        (1744831011u32, 18usize, 102usize),
                        (1744830467u32, 19usize, 101usize),
                        (1744831011u32, 19usize, 102usize),
                        (1744830467u32, 20usize, 101usize),
                        (1744831011u32, 20usize, 102usize),
                        (1744830467u32, 21usize, 101usize),
                        (1744831011u32, 21usize, 102usize),
                        (1744830467u32, 200usize, 0usize),
                        (1744830467u32, 216usize, 6usize),
                        (1744830467u32, 224usize, 3usize),
                        (1744830467u32, 0usize, 34usize),
                        (1744830467u32, 2usize, 34usize),
                        (268435454u32, 2usize, 97usize),
                        (268435454u32, 2usize, 106usize),
                        (1744830467u32, 2usize, 109usize),
                        (1744831011u32, 2usize, 110usize),
                        (1744830467u32, 6usize, 34usize),
                        (268435454u32, 17usize, 97usize),
                        (268435454u32, 17usize, 106usize),
                        (1744830467u32, 17usize, 109usize),
                        (1744831011u32, 17usize, 110usize),
                        (268435454u32, 18usize, 97usize),
                        (268435454u32, 18usize, 106usize),
                        (1744830467u32, 18usize, 109usize),
                        (1744831011u32, 18usize, 110usize),
                        (268435454u32, 19usize, 95usize),
                        (268435454u32, 19usize, 104usize),
                        (1744830467u32, 19usize, 109usize),
                        (1744831011u32, 19usize, 110usize),
                        (268435454u32, 20usize, 96usize),
                        (268435454u32, 20usize, 105usize),
                        (1744830467u32, 20usize, 109usize),
                        (1744831011u32, 20usize, 110usize),
                        (268435454u32, 21usize, 95usize),
                        (268435454u32, 21usize, 104usize),
                        (1744830467u32, 21usize, 109usize),
                        (1744831011u32, 21usize, 110usize),
                        (1744830467u32, 186usize, 1usize),
                        (1744830467u32, 186usize, 5usize),
                        (1744830467u32, 202usize, 3usize),
                        (1744830467u32, 202usize, 4usize),
                        (1744830467u32, 0usize, 31usize),
                        (1744970275u32, 1usize, 1usize),
                        (1343575382u32, 1usize, 17usize),
                        (270392798u32, 1usize, 18usize),
                        (1747067427u32, 1usize, 19usize),
                        (403492045u32, 1usize, 20usize),
                        (1611871028u32, 1usize, 21usize),
                        (1744831011u32, 1usize, 112usize),
                        (1611871028u32, 17usize, 17usize),
                        (137293551u32, 17usize, 18usize),
                        (1613968180u32, 17usize, 19usize),
                        (270392798u32, 17usize, 20usize),
                        (1478771781u32, 17usize, 21usize),
                        (1744831011u32, 17usize, 112usize),
                        (538688444u32, 18usize, 18usize),
                        (540785596u32, 18usize, 19usize),
                        (1210476135u32, 18usize, 20usize),
                        (405589197u32, 18usize, 21usize),
                        (1744831011u32, 18usize, 112usize),
                        (2097152u32, 19usize, 19usize),
                        (673884843u32, 19usize, 20usize),
                        (1882263826u32, 19usize, 21usize),
                        (1744831011u32, 19usize, 112usize),
                        (671787691u32, 20usize, 20usize),
                        (538688444u32, 20usize, 21usize),
                        (1744831011u32, 20usize, 112usize),
                        (1880166674u32, 21usize, 21usize),
                        (1744831011u32, 21usize, 112usize),
                        (1744830467u32, 187usize, 2usize),
                        (1744830467u32, 195usize, 5usize),
                        (1744830467u32, 195usize, 6usize),
                        (1744830467u32, 203usize, 3usize),
                        (1744830467u32, 203usize, 4usize),
                        (1744830467u32, 211usize, 1usize),
                        (1744830467u32, 1usize, 119usize),
                        (1744831011u32, 1usize, 120usize),
                        (1744830467u32, 2usize, 31usize),
                        (1744830467u32, 6usize, 31usize),
                        (1744830467u32, 17usize, 119usize),
                        (1744831011u32, 17usize, 120usize),
                        (1744830467u32, 18usize, 119usize),
                        (1744831011u32, 18usize, 120usize),
                        (1744830467u32, 19usize, 119usize),
                        (1744831011u32, 19usize, 120usize),
                        (1744830467u32, 20usize, 119usize),
                        (1744831011u32, 20usize, 120usize),
                        (1744830467u32, 21usize, 119usize),
                        (1744831011u32, 21usize, 120usize),
                        (1744830467u32, 203usize, 0usize),
                        (1744830467u32, 203usize, 5usize),
                        (1744830467u32, 219usize, 3usize),
                        (1744830467u32, 0usize, 35usize),
                        (1744830467u32, 1usize, 31usize),
                        (268435454u32, 1usize, 122usize),
                        (1744831011u32, 1usize, 128usize),
                        (1744830467u32, 5usize, 31usize),
                        (268435454u32, 17usize, 120usize),
                        (1744830467u32, 17usize, 127usize),
                        (1744831011u32, 17usize, 128usize),
                        (268435454u32, 17usize, 129usize),
                        (268435454u32, 18usize, 120usize),
                        (1744830467u32, 18usize, 127usize),
                        (1744831011u32, 18usize, 128usize),
                        (268435454u32, 18usize, 129usize),
                        (268435454u32, 19usize, 122usize),
                        (1744831011u32, 19usize, 128usize),
                        (268435454u32, 20usize, 121usize),
                        (1744830467u32, 20usize, 127usize),
                        (1744831011u32, 20usize, 128usize),
                        (268435454u32, 20usize, 130usize),
                        (268435454u32, 21usize, 122usize),
                        (1744831011u32, 21usize, 128usize),
                        (1744830467u32, 189usize, 2usize),
                        (1744830467u32, 197usize, 6usize),
                        (1744830467u32, 205usize, 3usize),
                        (1744830467u32, 205usize, 4usize),
                        (1744830467u32, 0usize, 32usize),
                        (1744970275u32, 1usize, 1usize),
                        (1343575382u32, 1usize, 17usize),
                        (270392798u32, 1usize, 18usize),
                        (1747067427u32, 1usize, 19usize),
                        (403492045u32, 1usize, 20usize),
                        (1611871028u32, 1usize, 21usize),
                        (268435454u32, 1usize, 112usize),
                        (1744830467u32, 1usize, 113usize),
                        (1744831011u32, 1usize, 114usize),
                        (1611871028u32, 17usize, 17usize),
                        (137293551u32, 17usize, 18usize),
                        (1613968180u32, 17usize, 19usize),
                        (270392798u32, 17usize, 20usize),
                        (1478771781u32, 17usize, 21usize),
                        (268435454u32, 17usize, 112usize),
                        (1744830467u32, 17usize, 113usize),
                        (1744831011u32, 17usize, 114usize),
                        (538688444u32, 18usize, 18usize),
                        (540785596u32, 18usize, 19usize),
                        (1210476135u32, 18usize, 20usize),
                        (405589197u32, 18usize, 21usize),
                        (268435454u32, 18usize, 112usize),
                        (1744830467u32, 18usize, 113usize),
                        (1744831011u32, 18usize, 114usize),
                        (2097152u32, 19usize, 19usize),
                        (673884843u32, 19usize, 20usize),
                        (1882263826u32, 19usize, 21usize),
                        (268435454u32, 19usize, 112usize),
                        (1744830467u32, 19usize, 113usize),
                        (1744831011u32, 19usize, 114usize),
                        (671787691u32, 20usize, 20usize),
                        (538688444u32, 20usize, 21usize),
                        (268435454u32, 20usize, 112usize),
                        (1744830467u32, 20usize, 113usize),
                        (1744831011u32, 20usize, 114usize),
                        (1880166674u32, 21usize, 21usize),
                        (268435454u32, 21usize, 112usize),
                        (1744830467u32, 21usize, 113usize),
                        (1744831011u32, 21usize, 114usize),
                        (1744830467u32, 188usize, 2usize),
                        (1744830467u32, 196usize, 5usize),
                        (1744830467u32, 196usize, 6usize),
                        (1744830467u32, 204usize, 3usize),
                        (1744830467u32, 204usize, 4usize),
                        (1744830467u32, 212usize, 1usize),
                        (1744830467u32, 1usize, 121usize),
                        (1744831011u32, 1usize, 122usize),
                        (1744830467u32, 2usize, 32usize),
                        (1744830467u32, 6usize, 32usize),
                        (1744830467u32, 17usize, 121usize),
                        (1744831011u32, 17usize, 122usize),
                        (1744830467u32, 18usize, 121usize),
                        (1744831011u32, 18usize, 122usize),
                        (1744830467u32, 19usize, 121usize),
                        (1744831011u32, 19usize, 122usize),
                        (1744830467u32, 20usize, 121usize),
                        (1744831011u32, 20usize, 122usize),
                        (1744830467u32, 21usize, 121usize),
                        (1744831011u32, 21usize, 122usize),
                        (1744830467u32, 204usize, 0usize),
                        (1744830467u32, 204usize, 5usize),
                        (1744830467u32, 220usize, 3usize),
                        (1744830467u32, 0usize, 36usize),
                        (1744830467u32, 1usize, 32usize),
                        (268435454u32, 1usize, 119usize),
                        (268435454u32, 1usize, 128usize),
                        (1744830467u32, 1usize, 129usize),
                        (1744831011u32, 1usize, 130usize),
                        (1744830467u32, 5usize, 32usize),
                        (268435454u32, 17usize, 121usize),
                        (1744830467u32, 17usize, 129usize),
                        (544u32, 17usize, 130usize),
                        (268435454u32, 18usize, 121usize),
                        (1744830467u32, 18usize, 129usize),
                        (544u32, 18usize, 130usize),
                        (268435454u32, 19usize, 119usize),
                        (268435454u32, 19usize, 128usize),
                        (1744830467u32, 19usize, 129usize),
                        (1744831011u32, 19usize, 130usize),
                        (268435454u32, 20usize, 122usize),
                        (268435454u32, 20usize, 127usize),
                        (1744830467u32, 20usize, 129usize),
                        (1744831011u32, 20usize, 130usize),
                        (268435454u32, 21usize, 119usize),
                        (268435454u32, 21usize, 128usize),
                        (1744830467u32, 21usize, 129usize),
                        (1744831011u32, 21usize, 130usize),
                        (1744830467u32, 190usize, 2usize),
                        (1744830467u32, 198usize, 6usize),
                        (1744830467u32, 206usize, 3usize),
                        (1744830467u32, 206usize, 4usize),
                        (1744830467u32, 0usize, 33usize),
                        (1744970275u32, 1usize, 1usize),
                        (1343575382u32, 1usize, 17usize),
                        (270392798u32, 1usize, 18usize),
                        (1747067427u32, 1usize, 19usize),
                        (403492045u32, 1usize, 20usize),
                        (1611871028u32, 1usize, 21usize),
                        (268435454u32, 1usize, 113usize),
                        (1744830467u32, 1usize, 115usize),
                        (1744831011u32, 1usize, 116usize),
                        (1611871028u32, 17usize, 17usize),
                        (137293551u32, 17usize, 18usize),
                        (1613968180u32, 17usize, 19usize),
                        (270392798u32, 17usize, 20usize),
                        (1478771781u32, 17usize, 21usize),
                        (268435454u32, 17usize, 113usize),
                        (1744830467u32, 17usize, 115usize),
                        (1744831011u32, 17usize, 116usize),
                        (538688444u32, 18usize, 18usize),
                        (540785596u32, 18usize, 19usize),
                        (1210476135u32, 18usize, 20usize),
                        (405589197u32, 18usize, 21usize),
                        (268435454u32, 18usize, 113usize),
                        (1744830467u32, 18usize, 115usize),
                        (1744831011u32, 18usize, 116usize),
                        (2097152u32, 19usize, 19usize),
                        (673884843u32, 19usize, 20usize),
                        (1882263826u32, 19usize, 21usize),
                        (268435454u32, 19usize, 113usize),
                        (1744830467u32, 19usize, 115usize),
                        (1744831011u32, 19usize, 116usize),
                        (671787691u32, 20usize, 20usize),
                        (538688444u32, 20usize, 21usize),
                        (268435454u32, 20usize, 113usize),
                        (1744830467u32, 20usize, 115usize),
                        (1744831011u32, 20usize, 116usize),
                        (1880166674u32, 21usize, 21usize),
                        (268435454u32, 21usize, 113usize),
                        (1744830467u32, 21usize, 115usize),
                        (1744831011u32, 21usize, 116usize),
                        (1744830467u32, 191usize, 2usize),
                        (1744830467u32, 199usize, 5usize),
                        (1744830467u32, 199usize, 6usize),
                        (1744830467u32, 207usize, 3usize),
                        (1744830467u32, 207usize, 4usize),
                        (1744830467u32, 215usize, 1usize),
                        (1744830467u32, 1usize, 123usize),
                        (1744831011u32, 1usize, 124usize),
                        (1744830467u32, 2usize, 33usize),
                        (1744830467u32, 6usize, 33usize),
                        (1744830467u32, 17usize, 123usize),
                        (1744831011u32, 17usize, 124usize),
                        (1744830467u32, 18usize, 123usize),
                        (1744831011u32, 18usize, 124usize),
                        (1744830467u32, 19usize, 123usize),
                        (1744831011u32, 19usize, 124usize),
                        (1744830467u32, 20usize, 123usize),
                        (1744831011u32, 20usize, 124usize),
                        (1744830467u32, 21usize, 123usize),
                        (1744831011u32, 21usize, 124usize),
                        (1744830467u32, 207usize, 0usize),
                        (1744830467u32, 207usize, 5usize),
                        (1744830467u32, 223usize, 3usize),
                        (1744830467u32, 0usize, 37usize),
                        (1744830467u32, 1usize, 33usize),
                        (268435454u32, 1usize, 120usize),
                        (268435454u32, 1usize, 129usize),
                        (1744830467u32, 1usize, 131usize),
                        (1744831011u32, 1usize, 132usize),
                        (1744830467u32, 5usize, 33usize),
                        (268435454u32, 17usize, 122usize),
                        (268435454u32, 17usize, 127usize),
                        (1744830467u32, 17usize, 131usize),
                        (1744831011u32, 17usize, 132usize),
                        (268435454u32, 18usize, 122usize),
                        (268435454u32, 18usize, 127usize),
                        (1744830467u32, 18usize, 131usize),
                        (1744831011u32, 18usize, 132usize),
                        (268435454u32, 19usize, 120usize),
                        (268435454u32, 19usize, 129usize),
                        (1744830467u32, 19usize, 131usize),
                        (1744831011u32, 19usize, 132usize),
                        (268435454u32, 20usize, 119usize),
                        (268435454u32, 20usize, 128usize),
                        (1744830467u32, 20usize, 131usize),
                        (1744831011u32, 20usize, 132usize),
                        (268435454u32, 21usize, 120usize),
                        (268435454u32, 21usize, 129usize),
                        (1744830467u32, 21usize, 131usize),
                        (1744831011u32, 21usize, 132usize),
                        (1744830467u32, 193usize, 2usize),
                        (1744830467u32, 201usize, 6usize),
                        (1744830467u32, 209usize, 3usize),
                        (1744830467u32, 209usize, 4usize),
                        (1744830467u32, 0usize, 34usize),
                        (1744970275u32, 1usize, 1usize),
                        (1343575382u32, 1usize, 17usize),
                        (270392798u32, 1usize, 18usize),
                        (1747067427u32, 1usize, 19usize),
                        (403492045u32, 1usize, 20usize),
                        (1611871028u32, 1usize, 21usize),
                        (268435454u32, 1usize, 114usize),
                        (1744830467u32, 1usize, 117usize),
                        (1744831011u32, 1usize, 118usize),
                        (1611871028u32, 17usize, 17usize),
                        (137293551u32, 17usize, 18usize),
                        (1613968180u32, 17usize, 19usize),
                        (270392798u32, 17usize, 20usize),
                        (1478771781u32, 17usize, 21usize),
                        (268435454u32, 17usize, 114usize),
                        (1744830467u32, 17usize, 117usize),
                        (1744831011u32, 17usize, 118usize),
                        (538688444u32, 18usize, 18usize),
                        (540785596u32, 18usize, 19usize),
                        (1210476135u32, 18usize, 20usize),
                        (405589197u32, 18usize, 21usize),
                        (268435454u32, 18usize, 114usize),
                        (1744830467u32, 18usize, 117usize),
                        (1744831011u32, 18usize, 118usize),
                        (2097152u32, 19usize, 19usize),
                        (673884843u32, 19usize, 20usize),
                        (1882263826u32, 19usize, 21usize),
                        (268435454u32, 19usize, 114usize),
                        (1744830467u32, 19usize, 117usize),
                        (1744831011u32, 19usize, 118usize),
                        (671787691u32, 20usize, 20usize),
                        (538688444u32, 20usize, 21usize),
                        (268435454u32, 20usize, 114usize),
                        (1744830467u32, 20usize, 117usize),
                        (1744831011u32, 20usize, 118usize),
                        (1880166674u32, 21usize, 21usize),
                        (268435454u32, 21usize, 114usize),
                        (1744830467u32, 21usize, 117usize),
                        (1744831011u32, 21usize, 118usize),
                        (1744830467u32, 192usize, 2usize),
                        (1744830467u32, 200usize, 5usize),
                        (1744830467u32, 200usize, 6usize),
                        (1744830467u32, 208usize, 3usize),
                        (1744830467u32, 208usize, 4usize),
                        (1744830467u32, 216usize, 1usize),
                        (1744830467u32, 1usize, 125usize),
                        (1744831011u32, 1usize, 126usize),
                        (1744830467u32, 2usize, 34usize),
                        (1744830467u32, 6usize, 34usize),
                        (1744830467u32, 17usize, 125usize),
                        (1744831011u32, 17usize, 126usize),
                        (1744830467u32, 18usize, 125usize),
                        (1744831011u32, 18usize, 126usize),
                        (1744830467u32, 19usize, 125usize),
                        (1744831011u32, 19usize, 126usize),
                        (1744830467u32, 20usize, 125usize),
                        (1744831011u32, 20usize, 126usize),
                        (1744830467u32, 21usize, 125usize),
                        (1744831011u32, 21usize, 126usize),
                        (1744830467u32, 208usize, 0usize),
                        (1744830467u32, 208usize, 5usize),
                        (1744830467u32, 224usize, 3usize),
                        (1744830467u32, 0usize, 38usize),
                        (1744830467u32, 1usize, 34usize),
                        (268435454u32, 1usize, 121usize),
                        (268435454u32, 1usize, 130usize),
                        (1744830467u32, 1usize, 133usize),
                        (1744831011u32, 1usize, 134usize),
                        (1744830467u32, 5usize, 34usize),
                        (268435454u32, 17usize, 119usize),
                        (268435454u32, 17usize, 128usize),
                        (1744830467u32, 17usize, 133usize),
                        (1744831011u32, 17usize, 134usize),
                        (268435454u32, 18usize, 119usize),
                        (268435454u32, 18usize, 128usize),
                        (1744830467u32, 18usize, 133usize),
                        (1744831011u32, 18usize, 134usize),
                        (268435454u32, 19usize, 121usize),
                        (268435454u32, 19usize, 130usize),
                        (1744830467u32, 19usize, 133usize),
                        (1744831011u32, 19usize, 134usize),
                        (268435454u32, 20usize, 120usize),
                        (268435454u32, 20usize, 129usize),
                        (1744830467u32, 20usize, 133usize),
                        (1744831011u32, 20usize, 134usize),
                        (268435454u32, 21usize, 121usize),
                        (268435454u32, 21usize, 130usize),
                        (1744830467u32, 21usize, 133usize),
                        (1744831011u32, 21usize, 134usize),
                        (1744830467u32, 194usize, 2usize),
                        (1744830467u32, 202usize, 6usize),
                        (1744830467u32, 210usize, 3usize),
                        (1744830467u32, 210usize, 4usize),
                        (1744830467u32, 0usize, 35usize),
                        (1476674629u32, 17usize, 17usize),
                        (940083337u32, 17usize, 18usize),
                        (2097152u32, 17usize, 19usize),
                        (1343575382u32, 17usize, 20usize),
                        (1747067427u32, 17usize, 21usize),
                        (1744831011u32, 17usize, 136usize),
                        (1476674629u32, 18usize, 18usize),
                        (2097152u32, 18usize, 19usize),
                        (1343575382u32, 18usize, 20usize),
                        (1747067427u32, 18usize, 21usize),
                        (1744831011u32, 18usize, 136usize),
                        (538688444u32, 19usize, 19usize),
                        (405589197u32, 19usize, 20usize),
                        (809081242u32, 19usize, 21usize),
                        (1744831011u32, 19usize, 136usize),
                        (1880166674u32, 20usize, 20usize),
                        (137293551u32, 20usize, 21usize),
                        (1744831011u32, 20usize, 136usize),
                        (270392798u32, 21usize, 21usize),
                        (1744831011u32, 21usize, 136usize),
                        (1744830467u32, 179usize, 6usize),
                        (1744830467u32, 187usize, 5usize),
                        (1744830467u32, 195usize, 1usize),
                        (1744830467u32, 203usize, 2usize),
                        (1744830467u32, 211usize, 3usize),
                        (1744830467u32, 211usize, 4usize),
                        (1744830467u32, 1usize, 31usize),
                        (1744830467u32, 5usize, 31usize),
                        (1744830467u32, 17usize, 143usize),
                        (1744831011u32, 17usize, 144usize),
                        (1744830467u32, 18usize, 143usize),
                        (1744831011u32, 18usize, 144usize),
                        (1744830467u32, 19usize, 143usize),
                        (1744831011u32, 19usize, 144usize),
                        (1744830467u32, 20usize, 143usize),
                        (1744831011u32, 20usize, 144usize),
                        (1744830467u32, 21usize, 143usize),
                        (1744831011u32, 21usize, 144usize),
                        (1744830467u32, 203usize, 6usize),
                        (1744830467u32, 211usize, 0usize),
                        (1744830467u32, 219usize, 2usize),
                        (1744830467u32, 219usize, 3usize),
                        (268435454u32, 17usize, 145usize),
                        (1744830467u32, 17usize, 151usize),
                        (1744831011u32, 17usize, 152usize),
                        (268435454u32, 17usize, 154usize),
                        (268435454u32, 18usize, 146usize),
                        (1744831011u32, 18usize, 152usize),
                        (268435454u32, 19usize, 143usize),
                        (1744830467u32, 19usize, 151usize),
                        (544u32, 19usize, 152usize),
                        (268435454u32, 20usize, 143usize),
                        (1744830467u32, 20usize, 151usize),
                        (544u32, 20usize, 152usize),
                        (268435454u32, 21usize, 146usize),
                        (1744831011u32, 21usize, 152usize),
                        (1744830467u32, 181usize, 6usize),
                        (1744830467u32, 189usize, 5usize),
                        (1744830467u32, 197usize, 1usize),
                        (1744830467u32, 205usize, 2usize),
                        (1744830467u32, 213usize, 3usize),
                        (1744830467u32, 213usize, 4usize),
                        (1744830467u32, 221usize, 0usize),
                        (1744830467u32, 0usize, 36usize),
                        (1476674629u32, 17usize, 17usize),
                        (940083337u32, 17usize, 18usize),
                        (2097152u32, 17usize, 19usize),
                        (1343575382u32, 17usize, 20usize),
                        (1747067427u32, 17usize, 21usize),
                        (268435454u32, 17usize, 136usize),
                        (1744830467u32, 17usize, 137usize),
                        (1744831011u32, 17usize, 138usize),
                        (1476674629u32, 18usize, 18usize),
                        (2097152u32, 18usize, 19usize),
                        (1343575382u32, 18usize, 20usize),
                        (1747067427u32, 18usize, 21usize),
                        (268435454u32, 18usize, 136usize),
                        (1744830467u32, 18usize, 137usize),
                        (1744831011u32, 18usize, 138usize),
                        (538688444u32, 19usize, 19usize),
                        (405589197u32, 19usize, 20usize),
                        (809081242u32, 19usize, 21usize),
                        (268435454u32, 19usize, 136usize),
                        (1744830467u32, 19usize, 137usize),
                        (1744831011u32, 19usize, 138usize),
                        (1880166674u32, 20usize, 20usize),
                        (137293551u32, 20usize, 21usize),
                        (268435454u32, 20usize, 136usize),
                        (1744830467u32, 20usize, 137usize),
                        (1744831011u32, 20usize, 138usize),
                        (270392798u32, 21usize, 21usize),
                        (268435454u32, 21usize, 136usize),
                        (1744830467u32, 21usize, 137usize),
                        (1744831011u32, 21usize, 138usize),
                        (1744830467u32, 180usize, 6usize),
                        (1744830467u32, 188usize, 5usize),
                        (1744830467u32, 196usize, 1usize),
                        (1744830467u32, 204usize, 2usize),
                        (1744830467u32, 212usize, 3usize),
                        (1744830467u32, 212usize, 4usize),
                        (1744830467u32, 1usize, 32usize),
                        (1744830467u32, 5usize, 32usize),
                        (1744830467u32, 17usize, 145usize),
                        (1744831011u32, 17usize, 146usize),
                        (1744830467u32, 18usize, 145usize),
                        (1744831011u32, 18usize, 146usize),
                        (1744830467u32, 19usize, 145usize),
                        (1744831011u32, 19usize, 146usize),
                        (1744830467u32, 20usize, 145usize),
                        (1744831011u32, 20usize, 146usize),
                        (1744830467u32, 21usize, 145usize),
                        (1744831011u32, 21usize, 146usize),
                        (1744830467u32, 204usize, 6usize),
                        (1744830467u32, 212usize, 0usize),
                        (1744830467u32, 220usize, 2usize),
                        (1744830467u32, 220usize, 3usize),
                        (268435454u32, 17usize, 146usize),
                        (268435454u32, 17usize, 151usize),
                        (1744830467u32, 17usize, 153usize),
                        (1744831011u32, 17usize, 154usize),
                        (268435454u32, 18usize, 143usize),
                        (268435454u32, 18usize, 152usize),
                        (1744830467u32, 18usize, 153usize),
                        (1744831011u32, 18usize, 154usize),
                        (268435454u32, 19usize, 144usize),
                        (1744831011u32, 19usize, 154usize),
                        (268435454u32, 20usize, 144usize),
                        (1744831011u32, 20usize, 154usize),
                        (268435454u32, 21usize, 143usize),
                        (268435454u32, 21usize, 152usize),
                        (1744830467u32, 21usize, 153usize),
                        (1744831011u32, 21usize, 154usize),
                        (1744830467u32, 182usize, 6usize),
                        (1744830467u32, 190usize, 5usize),
                        (1744830467u32, 198usize, 1usize),
                        (1744830467u32, 206usize, 2usize),
                        (1744830467u32, 214usize, 3usize),
                        (1744830467u32, 214usize, 4usize),
                        (1744830467u32, 222usize, 0usize),
                        (1744830467u32, 0usize, 37usize),
                        (1476674629u32, 17usize, 17usize),
                        (940083337u32, 17usize, 18usize),
                        (2097152u32, 17usize, 19usize),
                        (1343575382u32, 17usize, 20usize),
                        (1747067427u32, 17usize, 21usize),
                        (268435454u32, 17usize, 137usize),
                        (1744830467u32, 17usize, 139usize),
                        (1744831011u32, 17usize, 140usize),
                        (1476674629u32, 18usize, 18usize),
                        (2097152u32, 18usize, 19usize),
                        (1343575382u32, 18usize, 20usize),
                        (1747067427u32, 18usize, 21usize),
                        (268435454u32, 18usize, 137usize),
                        (1744830467u32, 18usize, 139usize),
                        (1744831011u32, 18usize, 140usize),
                        (538688444u32, 19usize, 19usize),
                        (405589197u32, 19usize, 20usize),
                        (809081242u32, 19usize, 21usize),
                        (268435454u32, 19usize, 137usize),
                        (1744830467u32, 19usize, 139usize),
                        (1744831011u32, 19usize, 140usize),
                        (1880166674u32, 20usize, 20usize),
                        (137293551u32, 20usize, 21usize),
                        (268435454u32, 20usize, 137usize),
                        (1744830467u32, 20usize, 139usize),
                        (1744831011u32, 20usize, 140usize),
                        (270392798u32, 21usize, 21usize),
                        (268435454u32, 21usize, 137usize),
                        (1744830467u32, 21usize, 139usize),
                        (1744831011u32, 21usize, 140usize),
                        (1744830467u32, 183usize, 6usize),
                        (1744830467u32, 191usize, 5usize),
                        (1744830467u32, 199usize, 1usize),
                        (1744830467u32, 207usize, 2usize),
                        (1744830467u32, 215usize, 3usize),
                        (1744830467u32, 215usize, 4usize),
                        (1744830467u32, 1usize, 33usize),
                        (1744830467u32, 5usize, 33usize),
                        (1744830467u32, 17usize, 147usize),
                        (1744831011u32, 17usize, 148usize),
                        (1744830467u32, 18usize, 147usize),
                        (1744831011u32, 18usize, 148usize),
                        (1744830467u32, 19usize, 147usize),
                        (1744831011u32, 19usize, 148usize),
                        (1744830467u32, 20usize, 147usize),
                        (1744831011u32, 20usize, 148usize),
                        (1744830467u32, 21usize, 147usize),
                        (1744831011u32, 21usize, 148usize),
                        (1744830467u32, 207usize, 6usize),
                        (1744830467u32, 215usize, 0usize),
                        (1744830467u32, 223usize, 2usize),
                        (1744830467u32, 223usize, 3usize),
                        (268435454u32, 17usize, 143usize),
                        (268435454u32, 17usize, 152usize),
                        (1744830467u32, 17usize, 155usize),
                        (1744831011u32, 17usize, 156usize),
                        (268435454u32, 18usize, 144usize),
                        (268435454u32, 18usize, 153usize),
                        (1744830467u32, 18usize, 155usize),
                        (1744831011u32, 18usize, 156usize),
                        (268435454u32, 19usize, 145usize),
                        (268435454u32, 19usize, 154usize),
                        (1744830467u32, 19usize, 155usize),
                        (1744831011u32, 19usize, 156usize),
                        (268435454u32, 20usize, 145usize),
                        (268435454u32, 20usize, 154usize),
                        (1744830467u32, 20usize, 155usize),
                        (1744831011u32, 20usize, 156usize),
                        (268435454u32, 21usize, 144usize),
                        (268435454u32, 21usize, 153usize),
                        (1744830467u32, 21usize, 155usize),
                        (1744831011u32, 21usize, 156usize),
                        (1744830467u32, 185usize, 6usize),
                        (1744830467u32, 193usize, 5usize),
                        (1744830467u32, 201usize, 1usize),
                        (1744830467u32, 209usize, 2usize),
                        (1744830467u32, 217usize, 3usize),
                        (1744830467u32, 217usize, 4usize),
                        (1744830467u32, 225usize, 0usize),
                        (1744830467u32, 0usize, 38usize),
                        (1476674629u32, 17usize, 17usize),
                        (940083337u32, 17usize, 18usize),
                        (2097152u32, 17usize, 19usize),
                        (1343575382u32, 17usize, 20usize),
                        (1747067427u32, 17usize, 21usize),
                        (268435454u32, 17usize, 138usize),
                        (1744830467u32, 17usize, 141usize),
                        (1744831011u32, 17usize, 142usize),
                        (1476674629u32, 18usize, 18usize),
                        (2097152u32, 18usize, 19usize),
                        (1343575382u32, 18usize, 20usize),
                        (1747067427u32, 18usize, 21usize),
                        (268435454u32, 18usize, 138usize),
                        (1744830467u32, 18usize, 141usize),
                        (1744831011u32, 18usize, 142usize),
                        (538688444u32, 19usize, 19usize),
                        (405589197u32, 19usize, 20usize),
                        (809081242u32, 19usize, 21usize),
                        (268435454u32, 19usize, 138usize),
                        (1744830467u32, 19usize, 141usize),
                        (1744831011u32, 19usize, 142usize),
                        (1880166674u32, 20usize, 20usize),
                        (137293551u32, 20usize, 21usize),
                        (268435454u32, 20usize, 138usize),
                        (1744830467u32, 20usize, 141usize),
                        (1744831011u32, 20usize, 142usize),
                        (270392798u32, 21usize, 21usize),
                        (268435454u32, 21usize, 138usize),
                        (1744830467u32, 21usize, 141usize),
                        (1744831011u32, 21usize, 142usize),
                        (1744830467u32, 184usize, 6usize),
                        (1744830467u32, 192usize, 5usize),
                        (1744830467u32, 200usize, 1usize),
                        (1744830467u32, 208usize, 2usize),
                        (1744830467u32, 216usize, 3usize),
                        (1744830467u32, 216usize, 4usize),
                        (1744830467u32, 1usize, 34usize),
                        (1744830467u32, 5usize, 34usize),
                        (1744830467u32, 17usize, 149usize),
                        (1744831011u32, 17usize, 150usize),
                        (1744830467u32, 18usize, 149usize),
                        (1744831011u32, 18usize, 150usize),
                        (1744830467u32, 19usize, 149usize),
                        (1744831011u32, 19usize, 150usize),
                        (1744830467u32, 20usize, 149usize),
                        (1744831011u32, 20usize, 150usize),
                        (1744830467u32, 21usize, 149usize),
                        (1744831011u32, 21usize, 150usize),
                        (1744830467u32, 208usize, 6usize),
                        (1744830467u32, 216usize, 0usize),
                        (1744830467u32, 224usize, 2usize),
                        (1744830467u32, 224usize, 3usize),
                        (268435454u32, 17usize, 144usize),
                        (268435454u32, 17usize, 153usize),
                        (1744830467u32, 17usize, 157usize),
                        (1744831011u32, 17usize, 158usize),
                        (268435454u32, 18usize, 145usize),
                        (268435454u32, 18usize, 154usize),
                        (1744830467u32, 18usize, 157usize),
                        (1744831011u32, 18usize, 158usize),
                        (268435454u32, 19usize, 146usize),
                        (268435454u32, 19usize, 151usize),
                        (1744830467u32, 19usize, 157usize),
                        (1744831011u32, 19usize, 158usize),
                        (268435454u32, 20usize, 146usize),
                        (268435454u32, 20usize, 151usize),
                        (1744830467u32, 20usize, 157usize),
                        (1744831011u32, 20usize, 158usize),
                        (268435454u32, 21usize, 145usize),
                        (268435454u32, 21usize, 154usize),
                        (1744830467u32, 21usize, 157usize),
                        (1744831011u32, 21usize, 158usize),
                        (1744830467u32, 186usize, 6usize),
                        (1744830467u32, 194usize, 5usize),
                        (1744830467u32, 202usize, 1usize),
                        (1744830467u32, 210usize, 2usize),
                        (1744830467u32, 218usize, 3usize),
                        (1744830467u32, 218usize, 4usize),
                        (1744830467u32, 226usize, 0usize),
                        (268435454u32, 187usize, 0usize),
                        (1744830467u32, 189usize, 0usize),
                        (268435454u32, 188usize, 0usize),
                        (1744830467u32, 190usize, 0usize),
                        (268435454u32, 191usize, 0usize),
                        (1744830467u32, 193usize, 0usize),
                        (268435454u32, 192usize, 0usize),
                        (1744830467u32, 194usize, 0usize),
                        (268435454u32, 195usize, 0usize),
                        (1744830467u32, 197usize, 0usize),
                        (268435454u32, 196usize, 0usize),
                        (1744830467u32, 198usize, 0usize),
                        (268435454u32, 199usize, 0usize),
                        (1744830467u32, 201usize, 0usize),
                        (268435454u32, 200usize, 0usize),
                        (1744830467u32, 202usize, 0usize),
                        (268435454u32, 203usize, 0usize),
                        (1744830467u32, 205usize, 0usize),
                        (268435454u32, 204usize, 0usize),
                        (1744830467u32, 206usize, 0usize),
                        (268435454u32, 207usize, 0usize),
                        (1744830467u32, 209usize, 0usize),
                        (268435454u32, 208usize, 0usize),
                        (1744830467u32, 210usize, 0usize),
                        (268435454u32, 211usize, 0usize),
                        (1744830467u32, 213usize, 0usize),
                        (268435454u32, 212usize, 0usize),
                        (1744830467u32, 214usize, 0usize),
                        (268435454u32, 215usize, 0usize),
                        (1744830467u32, 217usize, 0usize),
                        (268435454u32, 216usize, 0usize),
                        (1744830467u32, 218usize, 0usize),
                        (268435454u32, 187usize, 1usize),
                        (1744830467u32, 189usize, 1usize),
                        (268435454u32, 188usize, 1usize),
                        (1744830467u32, 190usize, 1usize),
                        (268435454u32, 191usize, 1usize),
                        (1744830467u32, 193usize, 1usize),
                        (268435454u32, 192usize, 1usize),
                        (1744830467u32, 194usize, 1usize),
                        (268435454u32, 203usize, 1usize),
                        (1744830467u32, 205usize, 1usize),
                        (268435454u32, 204usize, 1usize),
                        (1744830467u32, 206usize, 1usize),
                        (268435454u32, 207usize, 1usize),
                        (1744830467u32, 209usize, 1usize),
                        (268435454u32, 208usize, 1usize),
                        (1744830467u32, 210usize, 1usize),
                        (268435454u32, 211usize, 1usize),
                        (1744830467u32, 213usize, 1usize),
                        (268435454u32, 212usize, 1usize),
                        (1744830467u32, 214usize, 1usize),
                        (268435454u32, 215usize, 1usize),
                        (1744830467u32, 217usize, 1usize),
                        (268435454u32, 216usize, 1usize),
                        (1744830467u32, 218usize, 1usize),
                        (268435454u32, 179usize, 2usize),
                        (1744830467u32, 181usize, 2usize),
                        (268435454u32, 180usize, 2usize),
                        (1744830467u32, 182usize, 2usize),
                        (268435454u32, 183usize, 2usize),
                        (1744830467u32, 185usize, 2usize),
                        (268435454u32, 184usize, 2usize),
                        (1744830467u32, 186usize, 2usize),
                        (268435454u32, 195usize, 2usize),
                        (1744830467u32, 197usize, 2usize),
                        (268435454u32, 196usize, 2usize),
                        (1744830467u32, 198usize, 2usize),
                        (268435454u32, 199usize, 2usize),
                        (1744830467u32, 201usize, 2usize),
                        (268435454u32, 200usize, 2usize),
                        (1744830467u32, 202usize, 2usize),
                        (268435454u32, 219usize, 2usize),
                        (1744830467u32, 221usize, 2usize),
                        (268435454u32, 220usize, 2usize),
                        (1744830467u32, 222usize, 2usize),
                        (268435454u32, 223usize, 2usize),
                        (1744830467u32, 225usize, 2usize),
                        (268435454u32, 224usize, 2usize),
                        (1744830467u32, 226usize, 2usize),
                        (268435454u32, 219usize, 3usize),
                        (1744830467u32, 221usize, 3usize),
                        (268435454u32, 220usize, 3usize),
                        (1744830467u32, 222usize, 3usize),
                        (268435454u32, 223usize, 3usize),
                        (1744830467u32, 225usize, 3usize),
                        (268435454u32, 224usize, 3usize),
                        (1744830467u32, 226usize, 3usize),
                        (268435454u32, 219usize, 4usize),
                        (1744830467u32, 221usize, 4usize),
                        (268435454u32, 220usize, 4usize),
                        (1744830467u32, 222usize, 4usize),
                        (268435454u32, 223usize, 4usize),
                        (1744830467u32, 225usize, 4usize),
                        (268435454u32, 224usize, 4usize),
                        (1744830467u32, 226usize, 4usize),
                        (268435454u32, 179usize, 5usize),
                        (1744830467u32, 221usize, 5usize),
                        (268435454u32, 180usize, 5usize),
                        (1744830467u32, 222usize, 5usize),
                        (268435454u32, 183usize, 5usize),
                        (1744830467u32, 225usize, 5usize),
                        (268435454u32, 184usize, 5usize),
                        (1744830467u32, 226usize, 5usize),
                        (268435454u32, 195usize, 5usize),
                        (1744830467u32, 197usize, 5usize),
                        (268435454u32, 196usize, 5usize),
                        (1744830467u32, 198usize, 5usize),
                        (268435454u32, 199usize, 5usize),
                        (1744830467u32, 201usize, 5usize),
                        (268435454u32, 200usize, 5usize),
                        (1744830467u32, 202usize, 5usize),
                        (268435454u32, 203usize, 5usize),
                        (1744830467u32, 205usize, 5usize),
                        (268435454u32, 204usize, 5usize),
                        (1744830467u32, 206usize, 5usize),
                        (268435454u32, 207usize, 5usize),
                        (1744830467u32, 209usize, 5usize),
                        (268435454u32, 208usize, 5usize),
                        (1744830467u32, 210usize, 5usize),
                        (268435454u32, 203usize, 6usize),
                        (1744830467u32, 205usize, 6usize),
                        (268435454u32, 204usize, 6usize),
                        (1744830467u32, 206usize, 6usize),
                        (268435454u32, 207usize, 6usize),
                        (1744830467u32, 209usize, 6usize),
                        (268435454u32, 208usize, 6usize),
                        (1744830467u32, 210usize, 6usize),
                        (268435454u32, 211usize, 6usize),
                        (1744830467u32, 213usize, 6usize),
                        (268435454u32, 212usize, 6usize),
                        (1744830467u32, 214usize, 6usize),
                        (268435454u32, 215usize, 6usize),
                        (1744830467u32, 217usize, 6usize),
                        (268435454u32, 216usize, 6usize),
                        (1744830467u32, 218usize, 6usize),
                        (268435454u32, 219usize, 6usize),
                        (1744830467u32, 221usize, 6usize),
                        (268435454u32, 220usize, 6usize),
                        (1744830467u32, 222usize, 6usize),
                        (268435454u32, 223usize, 6usize),
                        (1744830467u32, 225usize, 6usize),
                        (268435454u32, 224usize, 6usize),
                        (1744830467u32, 226usize, 6usize),
                        (268435454u32, 0usize, 0usize),
                        (268435454u32, 1usize, 1usize),
                        (268435454u32, 2usize, 2usize),
                        (268435454u32, 3usize, 3usize),
                        (268435454u32, 4usize, 4usize),
                        (268435454u32, 5usize, 5usize),
                        (268435454u32, 6usize, 6usize),
                        (268435454u32, 7usize, 7usize),
                        (268435454u32, 8usize, 8usize),
                        (268435454u32, 9usize, 9usize),
                        (268435454u32, 10usize, 10usize),
                        (268435454u32, 11usize, 11usize),
                        (268435454u32, 12usize, 12usize),
                        (268435454u32, 13usize, 13usize),
                        (268435454u32, 14usize, 14usize),
                        (268435454u32, 15usize, 15usize),
                        (268435454u32, 16usize, 16usize),
                        (268435454u32, 159usize, 159usize),
                        (268435454u32, 160usize, 160usize),
                        (268435454u32, 161usize, 161usize),
                        (268435454u32, 162usize, 162usize),
                        (268435454u32, 163usize, 163usize),
                        (268435454u32, 164usize, 164usize),
                        (268435454u32, 165usize, 165usize),
                        (268435454u32, 166usize, 166usize),
                        (268435454u32, 167usize, 167usize),
                        (268435454u32, 168usize, 168usize),
                        (268435454u32, 169usize, 169usize),
                        (268435454u32, 170usize, 170usize),
                        (268435454u32, 171usize, 171usize),
                        (268435454u32, 172usize, 172usize),
                    ];
                    let mut _g: usize = 0;
                    while _g < 175usize {
                        let (pow, term_start, term_count) = CK_QUAD_GROUPS[_g];
                        let mut inner_sum: BabyBearExt4 = BabyBearExt4::ZERO;
                        let mut _t: usize = 0;
                        while _t < term_count {
                            let (coeff, idx_a, idx_b) = CK_QUAD_TERMS[term_start + _t];
                            let va = evals.get_unchecked(idx_a)[j];
                            let vb = evals.get_unchecked(idx_b)[j];
                            let mut prod = va;
                            field_ops::mul_assign(&mut prod, &vb);
                            field_ops::mul_assign_by_base(
                                &mut prod,
                                &BabyBearField::from_reduced_raw_repr(coeff),
                            );
                            field_ops::add_assign(&mut inner_sum, &prod);
                            _t += 1;
                        }
                        let mut t: BabyBearExt4 = *challenge_powers.get_unchecked(pow);
                        field_ops::mul_assign(&mut t, &inner_sum);
                        field_ops::add_assign(&mut result, &t);
                        _g += 1;
                    }
                }
                result
            };
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
                _ => {}
            }
            _sg += 1;
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
                _ => {}
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
                _ => {}
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
                _ => {}
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
                _ => {}
            }
            _sg += 1;
        }
    }
    acc
}
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn dim_reducing_6_compute_claim(
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
#[allow(clippy::needless_borrow, clippy::large_const_arrays)]
unsafe fn dim_reducing_6_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(2usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(3usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(0usize) };
        let v1 = unsafe { evals.get_unchecked(1usize) };
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
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn dim_reducing_7_compute_claim(
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
#[allow(clippy::needless_borrow, clippy::large_const_arrays)]
unsafe fn dim_reducing_7_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
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
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn dim_reducing_8_compute_claim(
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
#[allow(clippy::needless_borrow, clippy::large_const_arrays)]
unsafe fn dim_reducing_8_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
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
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn dim_reducing_9_compute_claim(
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
#[allow(clippy::needless_borrow, clippy::large_const_arrays)]
unsafe fn dim_reducing_9_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
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
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn dim_reducing_10_compute_claim(
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
#[allow(clippy::needless_borrow, clippy::large_const_arrays)]
unsafe fn dim_reducing_10_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
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
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn dim_reducing_11_compute_claim(
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
#[allow(clippy::needless_borrow, clippy::large_const_arrays)]
unsafe fn dim_reducing_11_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
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
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn dim_reducing_12_compute_claim(
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
#[allow(clippy::needless_borrow, clippy::large_const_arrays)]
unsafe fn dim_reducing_12_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
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
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn dim_reducing_13_compute_claim(
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
#[allow(clippy::needless_borrow, clippy::large_const_arrays)]
unsafe fn dim_reducing_13_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
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
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn dim_reducing_14_compute_claim(
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
#[allow(clippy::needless_borrow, clippy::large_const_arrays)]
unsafe fn dim_reducing_14_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
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
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn dim_reducing_15_compute_claim(
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
#[allow(clippy::needless_borrow, clippy::large_const_arrays)]
unsafe fn dim_reducing_15_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
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
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn dim_reducing_16_compute_claim(
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
#[allow(clippy::needless_borrow, clippy::large_const_arrays)]
unsafe fn dim_reducing_16_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
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
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn dim_reducing_17_compute_claim(
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
#[allow(clippy::needless_borrow, clippy::large_const_arrays)]
unsafe fn dim_reducing_17_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
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
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn dim_reducing_18_compute_claim(
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
#[allow(clippy::needless_borrow, clippy::large_const_arrays)]
unsafe fn dim_reducing_18_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
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
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn dim_reducing_19_compute_claim(
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
#[allow(clippy::needless_borrow, clippy::large_const_arrays)]
unsafe fn dim_reducing_19_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
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
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn dim_reducing_20_compute_claim(
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
#[allow(clippy::needless_borrow, clippy::large_const_arrays)]
unsafe fn dim_reducing_20_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
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
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn dim_reducing_21_compute_claim(
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
#[allow(clippy::needless_borrow, clippy::large_const_arrays)]
unsafe fn dim_reducing_21_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
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
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn dim_reducing_22_compute_claim(
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
#[allow(clippy::needless_borrow, clippy::large_const_arrays)]
unsafe fn dim_reducing_22_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
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
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn dim_reducing_23_compute_claim(
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
#[allow(clippy::needless_borrow, clippy::large_const_arrays)]
unsafe fn dim_reducing_23_final_step_accumulator(
    evals: &[[BabyBearExt4; 4]],
    batch_base: BabyBearExt4,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(0usize) };
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
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(1usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(2usize) };
        let v1 = unsafe { evals.get_unchecked(3usize) };
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
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(4usize) };
        let v1 = unsafe { evals.get_unchecked(5usize) };
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
        for _ in 0..GKR_TRANSCRIPT_U32 {
            transcript_buf.push(I::read_word());
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
        let mut seed = Blake2sTranscript::commit_initial(transcript_buf.as_slice());
        let mut hasher = DelegatedBlake2sState::new();
        let mut init_challenges = LazyVec::<BabyBearExt4, 3>::new();
        unsafe {
            init_challenges.set_len(3);
        }
        draw_field_els_into(&mut hasher, &mut seed, init_challenges.as_mut_slice());
        let lookup_alpha = *init_challenges.get(0);
        let lookup_additive_challenge = *init_challenges.get(1);
        let constraints_batch_challenge = *init_challenges.get(2);
        let mut evals_flat = LazyVec::<BabyBearExt4, GKR_EVALS>::new();
        unsafe {
            evals_flat.set_len(96usize);
        }
        read_field_els::<I>(evals_flat.as_mut_slice());
        let evals_slice = evals_flat.as_slice();
        commit_field_els(&mut seed, evals_slice);
        let mut all_challenges = LazyVec::<BabyBearExt4, { GKR_ROUNDS + 1 }>::new();
        unsafe {
            all_challenges.set_len(5usize);
        }
        draw_field_els_into(&mut hasher, &mut seed, all_challenges.as_mut_slice());
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
        let mut eval_buf = AlignedArray64::<u32, GKR_EVAL_BUF>::new_uninit();
        {
            let initial_claim =
                dim_reducing_23_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 3usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    23usize,
                )?;
            let mut fc_len = 3usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
                let f = dim_reducing_23_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    23usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
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
                dim_reducing_22_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 4usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    22usize,
                )?;
            let mut fc_len = 4usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
                let f = dim_reducing_22_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    22usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
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
                dim_reducing_21_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 5usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    21usize,
                )?;
            let mut fc_len = 5usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
                let f = dim_reducing_21_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    21usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
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
                dim_reducing_20_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 6usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    20usize,
                )?;
            let mut fc_len = 6usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
                let f = dim_reducing_20_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    20usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
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
                dim_reducing_19_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 7usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    19usize,
                )?;
            let mut fc_len = 7usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
                let f = dim_reducing_19_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    19usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
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
                dim_reducing_18_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 8usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    18usize,
                )?;
            let mut fc_len = 8usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
                let f = dim_reducing_18_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    18usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
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
                dim_reducing_17_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 9usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    17usize,
                )?;
            let mut fc_len = 9usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
                let f = dim_reducing_17_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    17usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
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
                dim_reducing_16_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 10usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    16usize,
                )?;
            let mut fc_len = 10usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
                let f = dim_reducing_16_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    16usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
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
                dim_reducing_15_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 11usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    15usize,
                )?;
            let mut fc_len = 11usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
                let f = dim_reducing_15_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    15usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
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
                dim_reducing_14_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 12usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    14usize,
                )?;
            let mut fc_len = 12usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
                let f = dim_reducing_14_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    14usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
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
                dim_reducing_13_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 13usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    13usize,
                )?;
            let mut fc_len = 13usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
                let f = dim_reducing_13_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    13usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
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
                dim_reducing_12_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 14usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    12usize,
                )?;
            let mut fc_len = 14usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
                let f = dim_reducing_12_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    12usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
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
                dim_reducing_11_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 15usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    11usize,
                )?;
            let mut fc_len = 15usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
                let f = dim_reducing_11_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    11usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
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
                dim_reducing_10_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 16usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    10usize,
                )?;
            let mut fc_len = 16usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
                let f = dim_reducing_10_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    10usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
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
                dim_reducing_9_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 17usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    9usize,
                )?;
            let mut fc_len = 17usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
                let f = dim_reducing_9_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    9usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
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
                dim_reducing_8_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 18usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    8usize,
                )?;
            let mut fc_len = 18usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
                let f = dim_reducing_8_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    8usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
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
                dim_reducing_7_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 19usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    7usize,
                )?;
            let mut fc_len = 19usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
                let f = dim_reducing_7_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    7usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
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
                dim_reducing_6_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 20usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    6usize,
                )?;
            let mut fc_len = 20usize;
            let data_words = 6usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
                let f = dim_reducing_6_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    6usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 6usize);
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
                verify_sumcheck_rounds::<I, 21usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    5usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 8usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 2]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
                let f = layer_5_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &challenge_powers,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    5usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
                verify_sumcheck_rounds::<I, 21usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    4usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 13usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 2]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 13usize);
                let f = layer_4_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &challenge_powers,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    4usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
                verify_sumcheck_rounds::<I, 21usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    3usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 25usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 2]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 25usize);
                let f = layer_3_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &challenge_powers,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    3usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
                verify_sumcheck_rounds::<I, 21usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    2usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 47usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 2]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 47usize);
                let f = layer_2_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &challenge_powers,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    2usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
                verify_sumcheck_rounds::<I, 21usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    1usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 90usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 2]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 90usize);
                let f = layer_1_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &challenge_powers,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    1usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
                verify_sumcheck_rounds::<I, 21usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    0usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 331usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 2]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 331usize);
                let f = layer_0_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &challenge_powers,
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    0usize,
                )?;
            }
            commit_eval_buffer(&mut eval_buf, &mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
            let last_r = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = last_r;
            fc_len += 1;
            let mut extra_evals = LazyVec::<BabyBearExt4, 44usize>::new();
            unsafe {
                extra_evals.set_len(44usize);
            }
            read_field_els::<I>(extra_evals.as_mut_slice());
            commit_field_els(&mut seed, extra_evals.as_slice());
            let final_step_evals: &[[BabyBearExt4; 2]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 331usize);
            state.prev_claims.clear();
            {
                const EXTRA_POS: [(usize, usize); 44usize] = [
                    (175usize, 0usize),
                    (176usize, 1usize),
                    (181usize, 2usize),
                    (182usize, 3usize),
                    (183usize, 4usize),
                    (184usize, 5usize),
                    (185usize, 6usize),
                    (186usize, 7usize),
                    (189usize, 8usize),
                    (192usize, 9usize),
                    (193usize, 10usize),
                    (198usize, 11usize),
                    (199usize, 12usize),
                    (202usize, 13usize),
                    (205usize, 14usize),
                    (206usize, 15usize),
                    (211usize, 16usize),
                    (212usize, 17usize),
                    (215usize, 18usize),
                    (218usize, 19usize),
                    (219usize, 20usize),
                    (224usize, 21usize),
                    (225usize, 22usize),
                    (228usize, 23usize),
                    (231usize, 24usize),
                    (232usize, 25usize),
                    (237usize, 26usize),
                    (238usize, 27usize),
                    (241usize, 28usize),
                    (244usize, 29usize),
                    (245usize, 30usize),
                    (250usize, 31usize),
                    (251usize, 32usize),
                    (254usize, 33usize),
                    (257usize, 34usize),
                    (258usize, 35usize),
                    (266usize, 36usize),
                    (267usize, 37usize),
                    (268usize, 38usize),
                    (269usize, 39usize),
                    (270usize, 40usize),
                    (271usize, 41usize),
                    (272usize, 42usize),
                    (273usize, 43usize),
                ];
                let mut regular_idx: usize = 0;
                let mut ep_idx: usize = 0;
                let mut merged_idx: usize = 0;
                while merged_idx < 375usize {
                    if ep_idx < 44usize && EXTRA_POS[ep_idx].0 == merged_idx {
                        state
                            .prev_claims
                            .push(*extra_evals.get(EXTRA_POS[ep_idx].1));
                        ep_idx += 1;
                    } else {
                        let ev = final_step_evals.get_unchecked(regular_idx);
                        let f0 = ev[0];
                        let mut diff = ev[1];
                        field_ops::sub_assign(&mut diff, &f0);
                        field_ops::mul_assign(&mut diff, &last_r);
                        field_ops::add_assign(&mut diff, &f0);
                        state.prev_claims.push(diff);
                        regular_idx += 1;
                    }
                    merged_idx += 1;
                }
            }
            {
                const SC_DESCS: [(usize, u32, usize, usize); 28usize] = [
                    (305usize, 1476395013u32, 0usize, 3usize),
                    (306usize, 133099247u32, 3usize, 3usize),
                    (307usize, 1476395013u32, 6usize, 3usize),
                    (308usize, 133099247u32, 9usize, 3usize),
                    (309usize, 1476395013u32, 12usize, 3usize),
                    (310usize, 133099247u32, 15usize, 3usize),
                    (311usize, 1476395013u32, 18usize, 3usize),
                    (312usize, 133099247u32, 21usize, 3usize),
                    (313usize, 1476395013u32, 24usize, 3usize),
                    (314usize, 133099247u32, 27usize, 3usize),
                    (315usize, 1476395013u32, 30usize, 3usize),
                    (316usize, 133099247u32, 33usize, 3usize),
                    (317usize, 1476395013u32, 36usize, 3usize),
                    (318usize, 133099247u32, 39usize, 3usize),
                    (319usize, 1476395013u32, 42usize, 3usize),
                    (320usize, 133099247u32, 45usize, 3usize),
                    (321usize, 1476395013u32, 48usize, 3usize),
                    (322usize, 133099247u32, 51usize, 3usize),
                    (323usize, 1476395013u32, 54usize, 3usize),
                    (324usize, 133099247u32, 57usize, 3usize),
                    (325usize, 1476395013u32, 60usize, 3usize),
                    (326usize, 133099247u32, 63usize, 3usize),
                    (327usize, 1476395013u32, 66usize, 3usize),
                    (328usize, 133099247u32, 69usize, 3usize),
                    (329usize, 1476395013u32, 72usize, 3usize),
                    (330usize, 133099247u32, 75usize, 3usize),
                    (331usize, 1476395013u32, 78usize, 3usize),
                    (332usize, 133099247u32, 81usize, 3usize),
                ];
                const SC_TERMS: [(u32, usize); 84usize] = [
                    (1744830467u32, 264usize),
                    (268435454u32, 175usize),
                    (133099247u32, 159usize),
                    (1744830467u32, 265usize),
                    (268435454u32, 176usize),
                    (1744830467u32, 159usize),
                    (1744830467u32, 264usize),
                    (268435454u32, 181usize),
                    (133099247u32, 160usize),
                    (1744830467u32, 265usize),
                    (268435454u32, 182usize),
                    (1744830467u32, 160usize),
                    (1744830467u32, 264usize),
                    (268435454u32, 185usize),
                    (133099247u32, 161usize),
                    (1744830467u32, 265usize),
                    (268435454u32, 186usize),
                    (1744830467u32, 161usize),
                    (1744830467u32, 264usize),
                    (268435454u32, 192usize),
                    (133099247u32, 162usize),
                    (1744830467u32, 265usize),
                    (268435454u32, 193usize),
                    (1744830467u32, 162usize),
                    (1744830467u32, 264usize),
                    (268435454u32, 198usize),
                    (133099247u32, 163usize),
                    (1744830467u32, 265usize),
                    (268435454u32, 199usize),
                    (1744830467u32, 163usize),
                    (1744830467u32, 264usize),
                    (268435454u32, 205usize),
                    (133099247u32, 164usize),
                    (1744830467u32, 265usize),
                    (268435454u32, 206usize),
                    (1744830467u32, 164usize),
                    (1744830467u32, 264usize),
                    (268435454u32, 211usize),
                    (133099247u32, 165usize),
                    (1744830467u32, 265usize),
                    (268435454u32, 212usize),
                    (1744830467u32, 165usize),
                    (1744830467u32, 264usize),
                    (268435454u32, 218usize),
                    (133099247u32, 166usize),
                    (1744830467u32, 265usize),
                    (268435454u32, 219usize),
                    (1744830467u32, 166usize),
                    (1744830467u32, 264usize),
                    (268435454u32, 224usize),
                    (133099247u32, 167usize),
                    (1744830467u32, 265usize),
                    (268435454u32, 225usize),
                    (1744830467u32, 167usize),
                    (1744830467u32, 264usize),
                    (268435454u32, 231usize),
                    (133099247u32, 168usize),
                    (1744830467u32, 265usize),
                    (268435454u32, 232usize),
                    (1744830467u32, 168usize),
                    (1744830467u32, 264usize),
                    (268435454u32, 237usize),
                    (133099247u32, 169usize),
                    (1744830467u32, 265usize),
                    (268435454u32, 238usize),
                    (1744830467u32, 169usize),
                    (1744830467u32, 264usize),
                    (268435454u32, 244usize),
                    (133099247u32, 170usize),
                    (1744830467u32, 265usize),
                    (268435454u32, 245usize),
                    (1744830467u32, 170usize),
                    (1744830467u32, 264usize),
                    (268435454u32, 250usize),
                    (133099247u32, 171usize),
                    (1744830467u32, 265usize),
                    (268435454u32, 251usize),
                    (1744830467u32, 171usize),
                    (1744830467u32, 264usize),
                    (268435454u32, 257usize),
                    (133099247u32, 172usize),
                    (1744830467u32, 265usize),
                    (268435454u32, 258usize),
                    (1744830467u32, 172usize),
                ];
                let mut _sc = 0;
                while _sc < 28usize {
                    let (cached_idx, constant, term_start, term_count) = SC_DESCS[_sc];
                    let mut expected: BabyBearExt4 =
                        <BabyBearExt4 as FieldExtension<BabyBearField>>::from_base(
                            BabyBearField::from_reduced_raw_repr(constant),
                        );
                    let mut _t = 0;
                    while _t < term_count {
                        let (coeff, dep_idx) = SC_TERMS[term_start + _t];
                        let mut t = *state.prev_claims.get_unchecked(dep_idx);
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(coeff),
                        );
                        field_ops::add_assign(&mut expected, &t);
                        _t += 1;
                    }
                    let cached = *state.prev_claims.get_unchecked(cached_idx);
                    if expected != cached {
                        return Err(GKRVerificationError::CacheRelationFailed { layer: 0usize });
                    }
                    _sc += 1;
                }
            }
            {
                const VL_DESCS: [(usize, usize, usize); 41usize] = [
                    (333usize, 0usize, 8usize),
                    (335usize, 8usize, 8usize),
                    (336usize, 16usize, 8usize),
                    (337usize, 24usize, 8usize),
                    (338usize, 32usize, 8usize),
                    (339usize, 40usize, 8usize),
                    (340usize, 48usize, 8usize),
                    (341usize, 56usize, 8usize),
                    (342usize, 64usize, 8usize),
                    (343usize, 72usize, 8usize),
                    (344usize, 80usize, 8usize),
                    (345usize, 88usize, 8usize),
                    (346usize, 96usize, 8usize),
                    (347usize, 104usize, 8usize),
                    (348usize, 112usize, 8usize),
                    (349usize, 120usize, 8usize),
                    (350usize, 128usize, 8usize),
                    (351usize, 136usize, 8usize),
                    (352usize, 144usize, 8usize),
                    (353usize, 152usize, 8usize),
                    (354usize, 160usize, 8usize),
                    (355usize, 168usize, 8usize),
                    (356usize, 176usize, 8usize),
                    (357usize, 184usize, 8usize),
                    (358usize, 192usize, 8usize),
                    (359usize, 200usize, 8usize),
                    (360usize, 208usize, 8usize),
                    (361usize, 216usize, 8usize),
                    (362usize, 224usize, 8usize),
                    (363usize, 232usize, 8usize),
                    (364usize, 240usize, 8usize),
                    (365usize, 248usize, 8usize),
                    (366usize, 256usize, 8usize),
                    (367usize, 264usize, 8usize),
                    (368usize, 272usize, 8usize),
                    (369usize, 280usize, 8usize),
                    (370usize, 288usize, 8usize),
                    (371usize, 296usize, 8usize),
                    (372usize, 304usize, 8usize),
                    (373usize, 312usize, 8usize),
                    (374usize, 320usize, 8usize),
                ];
                const VL_COLS: [(u32, usize, usize); 328usize] = [
                    (0u32, 0usize, 2usize),
                    (0u32, 2usize, 1usize),
                    (0u32, 3usize, 1usize),
                    (0u32, 4usize, 1usize),
                    (0u32, 5usize, 1usize),
                    (0u32, 6usize, 1usize),
                    (0u32, 7usize, 1usize),
                    (1879048114u32, 8usize, 0usize),
                    (0u32, 8usize, 1usize),
                    (0u32, 9usize, 1usize),
                    (0u32, 10usize, 1usize),
                    (0u32, 11usize, 0usize),
                    (0u32, 11usize, 0usize),
                    (0u32, 11usize, 0usize),
                    (0u32, 11usize, 0usize),
                    (0u32, 11usize, 7usize),
                    (0u32, 18usize, 1usize),
                    (0u32, 19usize, 1usize),
                    (0u32, 20usize, 1usize),
                    (0u32, 21usize, 0usize),
                    (0u32, 21usize, 0usize),
                    (0u32, 21usize, 0usize),
                    (0u32, 21usize, 0usize),
                    (0u32, 21usize, 7usize),
                    (0u32, 28usize, 1usize),
                    (0u32, 29usize, 1usize),
                    (0u32, 30usize, 1usize),
                    (0u32, 31usize, 0usize),
                    (0u32, 31usize, 0usize),
                    (0u32, 31usize, 0usize),
                    (0u32, 31usize, 0usize),
                    (0u32, 31usize, 7usize),
                    (0u32, 38usize, 1usize),
                    (0u32, 39usize, 1usize),
                    (0u32, 40usize, 1usize),
                    (0u32, 41usize, 0usize),
                    (0u32, 41usize, 0usize),
                    (0u32, 41usize, 0usize),
                    (0u32, 41usize, 0usize),
                    (0u32, 41usize, 7usize),
                    (0u32, 48usize, 1usize),
                    (0u32, 49usize, 1usize),
                    (0u32, 50usize, 1usize),
                    (0u32, 51usize, 0usize),
                    (0u32, 51usize, 0usize),
                    (0u32, 51usize, 0usize),
                    (0u32, 51usize, 0usize),
                    (0u32, 51usize, 7usize),
                    (0u32, 58usize, 1usize),
                    (0u32, 59usize, 1usize),
                    (0u32, 60usize, 1usize),
                    (0u32, 61usize, 0usize),
                    (0u32, 61usize, 0usize),
                    (0u32, 61usize, 0usize),
                    (0u32, 61usize, 0usize),
                    (0u32, 61usize, 7usize),
                    (0u32, 68usize, 1usize),
                    (0u32, 69usize, 1usize),
                    (0u32, 70usize, 1usize),
                    (0u32, 71usize, 0usize),
                    (0u32, 71usize, 0usize),
                    (0u32, 71usize, 0usize),
                    (0u32, 71usize, 0usize),
                    (0u32, 71usize, 7usize),
                    (0u32, 78usize, 1usize),
                    (0u32, 79usize, 1usize),
                    (0u32, 80usize, 1usize),
                    (0u32, 81usize, 0usize),
                    (0u32, 81usize, 0usize),
                    (0u32, 81usize, 0usize),
                    (0u32, 81usize, 0usize),
                    (0u32, 81usize, 7usize),
                    (0u32, 88usize, 1usize),
                    (0u32, 89usize, 1usize),
                    (0u32, 90usize, 1usize),
                    (0u32, 91usize, 0usize),
                    (0u32, 91usize, 0usize),
                    (0u32, 91usize, 0usize),
                    (0u32, 91usize, 0usize),
                    (0u32, 91usize, 7usize),
                    (0u32, 98usize, 1usize),
                    (0u32, 99usize, 1usize),
                    (0u32, 100usize, 1usize),
                    (0u32, 101usize, 0usize),
                    (0u32, 101usize, 0usize),
                    (0u32, 101usize, 0usize),
                    (0u32, 101usize, 0usize),
                    (0u32, 101usize, 7usize),
                    (0u32, 108usize, 1usize),
                    (0u32, 109usize, 1usize),
                    (0u32, 110usize, 1usize),
                    (0u32, 111usize, 0usize),
                    (0u32, 111usize, 0usize),
                    (0u32, 111usize, 0usize),
                    (0u32, 111usize, 0usize),
                    (0u32, 111usize, 7usize),
                    (0u32, 118usize, 1usize),
                    (0u32, 119usize, 1usize),
                    (0u32, 120usize, 1usize),
                    (0u32, 121usize, 0usize),
                    (0u32, 121usize, 0usize),
                    (0u32, 121usize, 0usize),
                    (0u32, 121usize, 0usize),
                    (0u32, 121usize, 7usize),
                    (0u32, 128usize, 1usize),
                    (0u32, 129usize, 1usize),
                    (0u32, 130usize, 1usize),
                    (0u32, 131usize, 0usize),
                    (0u32, 131usize, 0usize),
                    (0u32, 131usize, 0usize),
                    (0u32, 131usize, 0usize),
                    (0u32, 131usize, 7usize),
                    (0u32, 138usize, 1usize),
                    (0u32, 139usize, 1usize),
                    (0u32, 140usize, 1usize),
                    (0u32, 141usize, 0usize),
                    (0u32, 141usize, 0usize),
                    (0u32, 141usize, 0usize),
                    (0u32, 141usize, 0usize),
                    (0u32, 141usize, 7usize),
                    (0u32, 148usize, 1usize),
                    (0u32, 149usize, 1usize),
                    (0u32, 150usize, 1usize),
                    (0u32, 151usize, 0usize),
                    (0u32, 151usize, 0usize),
                    (0u32, 151usize, 0usize),
                    (0u32, 151usize, 0usize),
                    (0u32, 151usize, 7usize),
                    (0u32, 158usize, 1usize),
                    (0u32, 159usize, 1usize),
                    (0u32, 160usize, 1usize),
                    (0u32, 161usize, 0usize),
                    (0u32, 161usize, 0usize),
                    (0u32, 161usize, 0usize),
                    (0u32, 161usize, 0usize),
                    (0u32, 161usize, 7usize),
                    (0u32, 168usize, 1usize),
                    (0u32, 169usize, 1usize),
                    (0u32, 170usize, 1usize),
                    (0u32, 171usize, 0usize),
                    (0u32, 171usize, 0usize),
                    (0u32, 171usize, 0usize),
                    (0u32, 171usize, 0usize),
                    (0u32, 171usize, 7usize),
                    (0u32, 178usize, 1usize),
                    (0u32, 179usize, 1usize),
                    (0u32, 180usize, 1usize),
                    (0u32, 181usize, 0usize),
                    (0u32, 181usize, 0usize),
                    (0u32, 181usize, 0usize),
                    (0u32, 181usize, 0usize),
                    (0u32, 181usize, 7usize),
                    (0u32, 188usize, 1usize),
                    (0u32, 189usize, 1usize),
                    (0u32, 190usize, 1usize),
                    (0u32, 191usize, 0usize),
                    (0u32, 191usize, 0usize),
                    (0u32, 191usize, 0usize),
                    (0u32, 191usize, 0usize),
                    (0u32, 191usize, 7usize),
                    (0u32, 198usize, 1usize),
                    (0u32, 199usize, 1usize),
                    (0u32, 200usize, 1usize),
                    (0u32, 201usize, 0usize),
                    (0u32, 201usize, 0usize),
                    (0u32, 201usize, 0usize),
                    (0u32, 201usize, 0usize),
                    (0u32, 201usize, 7usize),
                    (0u32, 208usize, 1usize),
                    (0u32, 209usize, 1usize),
                    (0u32, 210usize, 1usize),
                    (0u32, 211usize, 0usize),
                    (0u32, 211usize, 0usize),
                    (0u32, 211usize, 0usize),
                    (0u32, 211usize, 0usize),
                    (0u32, 211usize, 7usize),
                    (0u32, 218usize, 1usize),
                    (0u32, 219usize, 1usize),
                    (0u32, 220usize, 1usize),
                    (0u32, 221usize, 0usize),
                    (0u32, 221usize, 0usize),
                    (0u32, 221usize, 0usize),
                    (0u32, 221usize, 0usize),
                    (0u32, 221usize, 7usize),
                    (0u32, 228usize, 1usize),
                    (0u32, 229usize, 1usize),
                    (0u32, 230usize, 1usize),
                    (0u32, 231usize, 0usize),
                    (0u32, 231usize, 0usize),
                    (0u32, 231usize, 0usize),
                    (0u32, 231usize, 0usize),
                    (0u32, 231usize, 7usize),
                    (0u32, 238usize, 1usize),
                    (0u32, 239usize, 1usize),
                    (0u32, 240usize, 1usize),
                    (0u32, 241usize, 0usize),
                    (0u32, 241usize, 0usize),
                    (0u32, 241usize, 0usize),
                    (0u32, 241usize, 0usize),
                    (0u32, 241usize, 7usize),
                    (0u32, 248usize, 1usize),
                    (0u32, 249usize, 1usize),
                    (0u32, 250usize, 1usize),
                    (0u32, 251usize, 0usize),
                    (0u32, 251usize, 0usize),
                    (0u32, 251usize, 0usize),
                    (0u32, 251usize, 0usize),
                    (0u32, 251usize, 7usize),
                    (0u32, 258usize, 1usize),
                    (0u32, 259usize, 1usize),
                    (0u32, 260usize, 1usize),
                    (0u32, 261usize, 0usize),
                    (0u32, 261usize, 0usize),
                    (0u32, 261usize, 0usize),
                    (0u32, 261usize, 0usize),
                    (0u32, 261usize, 7usize),
                    (0u32, 268usize, 1usize),
                    (0u32, 269usize, 1usize),
                    (0u32, 270usize, 1usize),
                    (0u32, 271usize, 0usize),
                    (0u32, 271usize, 0usize),
                    (0u32, 271usize, 0usize),
                    (0u32, 271usize, 0usize),
                    (0u32, 271usize, 7usize),
                    (0u32, 278usize, 1usize),
                    (0u32, 279usize, 1usize),
                    (0u32, 280usize, 1usize),
                    (0u32, 281usize, 0usize),
                    (0u32, 281usize, 0usize),
                    (0u32, 281usize, 0usize),
                    (0u32, 281usize, 0usize),
                    (0u32, 281usize, 7usize),
                    (0u32, 288usize, 1usize),
                    (0u32, 289usize, 1usize),
                    (0u32, 290usize, 1usize),
                    (0u32, 291usize, 0usize),
                    (0u32, 291usize, 0usize),
                    (0u32, 291usize, 0usize),
                    (0u32, 291usize, 0usize),
                    (0u32, 291usize, 7usize),
                    (0u32, 298usize, 1usize),
                    (0u32, 299usize, 1usize),
                    (0u32, 300usize, 1usize),
                    (0u32, 301usize, 0usize),
                    (0u32, 301usize, 0usize),
                    (0u32, 301usize, 0usize),
                    (0u32, 301usize, 0usize),
                    (0u32, 301usize, 7usize),
                    (0u32, 308usize, 1usize),
                    (0u32, 309usize, 1usize),
                    (0u32, 310usize, 1usize),
                    (0u32, 311usize, 0usize),
                    (0u32, 311usize, 0usize),
                    (0u32, 311usize, 0usize),
                    (0u32, 311usize, 0usize),
                    (0u32, 311usize, 7usize),
                    (0u32, 318usize, 1usize),
                    (0u32, 319usize, 1usize),
                    (0u32, 320usize, 1usize),
                    (0u32, 321usize, 0usize),
                    (0u32, 321usize, 0usize),
                    (0u32, 321usize, 0usize),
                    (0u32, 321usize, 0usize),
                    (0u32, 321usize, 7usize),
                    (0u32, 328usize, 1usize),
                    (0u32, 329usize, 1usize),
                    (0u32, 330usize, 1usize),
                    (0u32, 331usize, 0usize),
                    (0u32, 331usize, 0usize),
                    (0u32, 331usize, 0usize),
                    (0u32, 331usize, 0usize),
                    (0u32, 331usize, 7usize),
                    (0u32, 338usize, 1usize),
                    (0u32, 339usize, 1usize),
                    (0u32, 340usize, 1usize),
                    (0u32, 341usize, 0usize),
                    (0u32, 341usize, 0usize),
                    (0u32, 341usize, 0usize),
                    (0u32, 341usize, 0usize),
                    (0u32, 341usize, 7usize),
                    (0u32, 348usize, 1usize),
                    (0u32, 349usize, 1usize),
                    (0u32, 350usize, 1usize),
                    (0u32, 351usize, 0usize),
                    (0u32, 351usize, 0usize),
                    (0u32, 351usize, 0usize),
                    (0u32, 351usize, 0usize),
                    (0u32, 351usize, 7usize),
                    (0u32, 358usize, 1usize),
                    (0u32, 359usize, 1usize),
                    (0u32, 360usize, 1usize),
                    (0u32, 361usize, 0usize),
                    (0u32, 361usize, 0usize),
                    (0u32, 361usize, 0usize),
                    (0u32, 361usize, 0usize),
                    (0u32, 361usize, 7usize),
                    (0u32, 368usize, 1usize),
                    (0u32, 369usize, 1usize),
                    (0u32, 370usize, 1usize),
                    (0u32, 371usize, 0usize),
                    (0u32, 371usize, 0usize),
                    (0u32, 371usize, 0usize),
                    (0u32, 371usize, 0usize),
                    (0u32, 371usize, 7usize),
                    (0u32, 378usize, 1usize),
                    (0u32, 379usize, 1usize),
                    (0u32, 380usize, 1usize),
                    (0u32, 381usize, 0usize),
                    (0u32, 381usize, 0usize),
                    (0u32, 381usize, 0usize),
                    (0u32, 381usize, 0usize),
                    (0u32, 381usize, 7usize),
                    (0u32, 388usize, 1usize),
                    (0u32, 389usize, 1usize),
                    (0u32, 390usize, 1usize),
                    (0u32, 391usize, 0usize),
                    (0u32, 391usize, 0usize),
                    (0u32, 391usize, 0usize),
                    (0u32, 391usize, 0usize),
                    (0u32, 391usize, 7usize),
                    (0u32, 398usize, 1usize),
                    (0u32, 399usize, 1usize),
                    (0u32, 400usize, 1usize),
                    (0u32, 401usize, 0usize),
                    (0u32, 401usize, 0usize),
                    (0u32, 401usize, 0usize),
                    (0u32, 401usize, 0usize),
                    (0u32, 401usize, 7usize),
                ];
                const VL_TERMS: [(u32, usize); 408usize] = [
                    (134213359u32, 263usize),
                    (268435454u32, 177usize),
                    (268435454u32, 189usize),
                    (268435454u32, 202usize),
                    (268435454u32, 215usize),
                    (268435454u32, 228usize),
                    (268435454u32, 241usize),
                    (268435454u32, 254usize),
                    (268435454u32, 39usize),
                    (268435454u32, 47usize),
                    (268435454u32, 55usize),
                    (134217647u32, 0usize),
                    (671088555u32, 1usize),
                    (671088555u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (402653101u32, 6usize),
                    (268435454u32, 40usize),
                    (268435454u32, 48usize),
                    (268435454u32, 56usize),
                    (134217647u32, 0usize),
                    (671088555u32, 1usize),
                    (671088555u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (402653101u32, 6usize),
                    (268435454u32, 41usize),
                    (268435454u32, 49usize),
                    (268435454u32, 57usize),
                    (134217647u32, 0usize),
                    (671088555u32, 1usize),
                    (671088555u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (402653101u32, 6usize),
                    (268435454u32, 42usize),
                    (268435454u32, 50usize),
                    (268435454u32, 58usize),
                    (134217647u32, 0usize),
                    (671088555u32, 1usize),
                    (671088555u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (402653101u32, 6usize),
                    (268435454u32, 43usize),
                    (268435454u32, 51usize),
                    (268435454u32, 59usize),
                    (134217647u32, 0usize),
                    (671088555u32, 1usize),
                    (671088555u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (402653101u32, 6usize),
                    (268435454u32, 44usize),
                    (268435454u32, 52usize),
                    (268435454u32, 60usize),
                    (134217647u32, 0usize),
                    (671088555u32, 1usize),
                    (671088555u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (402653101u32, 6usize),
                    (268435454u32, 45usize),
                    (268435454u32, 53usize),
                    (268435454u32, 61usize),
                    (134217647u32, 0usize),
                    (671088555u32, 1usize),
                    (671088555u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (402653101u32, 6usize),
                    (268435454u32, 46usize),
                    (268435454u32, 54usize),
                    (268435454u32, 62usize),
                    (134217647u32, 0usize),
                    (671088555u32, 1usize),
                    (671088555u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (402653101u32, 6usize),
                    (268435454u32, 63usize),
                    (268435454u32, 71usize),
                    (268435454u32, 79usize),
                    (1073741816u32, 0usize),
                    (671088555u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 64usize),
                    (268435454u32, 72usize),
                    (268435454u32, 80usize),
                    (1073741816u32, 0usize),
                    (671088555u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 65usize),
                    (268435454u32, 73usize),
                    (268435454u32, 81usize),
                    (1073741816u32, 0usize),
                    (671088555u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 66usize),
                    (268435454u32, 74usize),
                    (268435454u32, 82usize),
                    (1073741816u32, 0usize),
                    (671088555u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 67usize),
                    (268435454u32, 75usize),
                    (268435454u32, 83usize),
                    (1073741816u32, 0usize),
                    (671088555u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 68usize),
                    (268435454u32, 76usize),
                    (268435454u32, 84usize),
                    (1073741816u32, 0usize),
                    (671088555u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 69usize),
                    (268435454u32, 77usize),
                    (268435454u32, 85usize),
                    (1073741816u32, 0usize),
                    (671088555u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 70usize),
                    (268435454u32, 78usize),
                    (268435454u32, 86usize),
                    (1073741816u32, 0usize),
                    (671088555u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 87usize),
                    (268435454u32, 95usize),
                    (268435454u32, 103usize),
                    (1073741816u32, 0usize),
                    (1073741816u32, 1usize),
                    (671088555u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (1073741816u32, 5usize),
                    (402653101u32, 6usize),
                    (268435454u32, 88usize),
                    (268435454u32, 96usize),
                    (268435454u32, 104usize),
                    (1073741816u32, 0usize),
                    (1073741816u32, 1usize),
                    (671088555u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (1073741816u32, 5usize),
                    (402653101u32, 6usize),
                    (268435454u32, 89usize),
                    (268435454u32, 97usize),
                    (268435454u32, 105usize),
                    (1073741816u32, 0usize),
                    (1073741816u32, 1usize),
                    (671088555u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (1073741816u32, 5usize),
                    (402653101u32, 6usize),
                    (268435454u32, 90usize),
                    (268435454u32, 98usize),
                    (268435454u32, 106usize),
                    (1073741816u32, 0usize),
                    (1073741816u32, 1usize),
                    (671088555u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (1073741816u32, 5usize),
                    (402653101u32, 6usize),
                    (268435454u32, 91usize),
                    (268435454u32, 99usize),
                    (268435454u32, 107usize),
                    (1073741816u32, 0usize),
                    (1073741816u32, 1usize),
                    (671088555u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (1073741816u32, 5usize),
                    (402653101u32, 6usize),
                    (268435454u32, 92usize),
                    (268435454u32, 100usize),
                    (268435454u32, 108usize),
                    (1073741816u32, 0usize),
                    (1073741816u32, 1usize),
                    (671088555u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (1073741816u32, 5usize),
                    (402653101u32, 6usize),
                    (268435454u32, 93usize),
                    (268435454u32, 101usize),
                    (268435454u32, 109usize),
                    (1073741816u32, 0usize),
                    (1073741816u32, 1usize),
                    (671088555u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (1073741816u32, 5usize),
                    (402653101u32, 6usize),
                    (268435454u32, 94usize),
                    (268435454u32, 102usize),
                    (268435454u32, 110usize),
                    (1073741816u32, 0usize),
                    (1073741816u32, 1usize),
                    (671088555u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (1073741816u32, 5usize),
                    (402653101u32, 6usize),
                    (268435454u32, 111usize),
                    (268435454u32, 119usize),
                    (268435454u32, 127usize),
                    (1073741816u32, 0usize),
                    (671088555u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 112usize),
                    (268435454u32, 120usize),
                    (268435454u32, 128usize),
                    (1073741816u32, 0usize),
                    (671088555u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 113usize),
                    (268435454u32, 121usize),
                    (268435454u32, 129usize),
                    (1073741816u32, 0usize),
                    (671088555u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 114usize),
                    (268435454u32, 122usize),
                    (268435454u32, 130usize),
                    (1073741816u32, 0usize),
                    (671088555u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 115usize),
                    (268435454u32, 123usize),
                    (268435454u32, 131usize),
                    (1073741816u32, 0usize),
                    (671088555u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 116usize),
                    (268435454u32, 124usize),
                    (268435454u32, 132usize),
                    (1073741816u32, 0usize),
                    (671088555u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 117usize),
                    (268435454u32, 125usize),
                    (268435454u32, 133usize),
                    (1073741816u32, 0usize),
                    (671088555u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 118usize),
                    (268435454u32, 126usize),
                    (268435454u32, 134usize),
                    (1073741816u32, 0usize),
                    (671088555u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (402653101u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 135usize),
                    (268435454u32, 143usize),
                    (268435454u32, 151usize),
                    (1073741816u32, 0usize),
                    (1073741816u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (1073741816u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 136usize),
                    (268435454u32, 144usize),
                    (268435454u32, 152usize),
                    (1073741816u32, 0usize),
                    (1073741816u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (1073741816u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 137usize),
                    (268435454u32, 145usize),
                    (268435454u32, 153usize),
                    (1073741816u32, 0usize),
                    (1073741816u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (1073741816u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 138usize),
                    (268435454u32, 146usize),
                    (268435454u32, 154usize),
                    (1073741816u32, 0usize),
                    (1073741816u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (1073741816u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 139usize),
                    (268435454u32, 147usize),
                    (268435454u32, 155usize),
                    (1073741816u32, 0usize),
                    (1073741816u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (1073741816u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 140usize),
                    (268435454u32, 148usize),
                    (268435454u32, 156usize),
                    (1073741816u32, 0usize),
                    (1073741816u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (1073741816u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 141usize),
                    (268435454u32, 149usize),
                    (268435454u32, 157usize),
                    (1073741816u32, 0usize),
                    (1073741816u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (1073741816u32, 5usize),
                    (1073741816u32, 6usize),
                    (268435454u32, 142usize),
                    (268435454u32, 150usize),
                    (268435454u32, 158usize),
                    (1073741816u32, 0usize),
                    (1073741816u32, 1usize),
                    (1073741816u32, 2usize),
                    (1073741816u32, 3usize),
                    (671088555u32, 4usize),
                    (1073741816u32, 5usize),
                    (1073741816u32, 6usize),
                ];
                let mut _vl = 0;
                while _vl < 41usize {
                    let (cached_idx, col_start, col_count) = VL_DESCS[_vl];
                    let mut expected: BabyBearExt4 = BabyBearExt4::ZERO;
                    let mut alpha_power: BabyBearExt4 = BabyBearExt4::ONE;
                    let mut _c = 0;
                    while _c < col_count {
                        let (col_constant, term_start, term_count) = VL_COLS[col_start + _c];
                        let mut col_val: BabyBearExt4 =
                            <BabyBearExt4 as FieldExtension<BabyBearField>>::from_base(
                                BabyBearField::from_reduced_raw_repr(col_constant),
                            );
                        let mut _t = 0;
                        while _t < term_count {
                            let (coeff, dep_idx) = VL_TERMS[term_start + _t];
                            let mut t = *state.prev_claims.get_unchecked(dep_idx);
                            field_ops::mul_assign_by_base(
                                &mut t,
                                &BabyBearField::from_reduced_raw_repr(coeff),
                            );
                            field_ops::add_assign(&mut col_val, &t);
                            _t += 1;
                        }
                        let mut term = col_val;
                        field_ops::mul_assign(&mut term, &alpha_power);
                        field_ops::add_assign(&mut expected, &term);
                        field_ops::mul_assign(&mut alpha_power, &lookup_alpha);
                        _c += 1;
                    }
                    let cached = *state.prev_claims.get_unchecked(cached_idx);
                    if expected != cached {
                        return Err(GKRVerificationError::CacheRelationFailed { layer: 0usize });
                    }
                    _vl += 1;
                }
            }
            {
                const VS_DESCS: [(usize, usize, usize); 1usize] = [(334usize, 0usize, 8usize)];
                const VS_DEPS: [usize; 8usize] = [
                    266usize, 267usize, 268usize, 269usize, 270usize, 271usize, 272usize, 273usize,
                ];
                let mut _vs = 0;
                while _vs < 1usize {
                    let (cached_idx, dep_start, dep_count) = VS_DESCS[_vs];
                    let mut expected: BabyBearExt4 = BabyBearExt4::ZERO;
                    let mut alpha_power: BabyBearExt4 = BabyBearExt4::ONE;
                    let mut _d = 0;
                    while _d < dep_count {
                        let dep_idx = VS_DEPS[dep_start + _d];
                        let mut term = *state.prev_claims.get_unchecked(dep_idx);
                        field_ops::mul_assign(&mut term, &alpha_power);
                        field_ops::add_assign(&mut expected, &term);
                        field_ops::mul_assign(&mut alpha_power, &lookup_alpha);
                        _d += 1;
                    }
                    let cached = *state.prev_claims.get_unchecked(cached_idx);
                    if expected != cached {
                        return Err(GKRVerificationError::CacheRelationFailed { layer: 0usize });
                    }
                    _vs += 1;
                }
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
        }
        let mut draw_buf = LazyVec::<BabyBearExt4, 1>::new();
        unsafe {
            draw_buf.set_len(1);
        }
        draw_field_els_into(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
            whir_transcript_seed: seed,
            setup_cap,
            memory_cap,
            witness_cap,
        })
    }
}
