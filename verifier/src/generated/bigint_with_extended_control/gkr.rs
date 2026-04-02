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
    const DESCS: [(usize, usize, usize); 102usize] = [
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
    ];
    let mut combined = BabyBearExt4::ZERO;
    let mut current_batch = BabyBearExt4::ONE;
    let mut i = 0;
    while i < 102usize {
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
        const SIMPLE_GATES: [(usize, [usize; 4]); 21usize] = [
            (1usize, [212usize, 0usize, 0usize, 0usize]),
            (2usize, [217usize, 218usize, 0usize, 0usize]),
            (2usize, [219usize, 220usize, 0usize, 0usize]),
            (2usize, [221usize, 222usize, 0usize, 0usize]),
            (2usize, [223usize, 224usize, 0usize, 0usize]),
            (2usize, [225usize, 226usize, 0usize, 0usize]),
            (2usize, [227usize, 228usize, 0usize, 0usize]),
            (2usize, [229usize, 230usize, 0usize, 0usize]),
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
        ];
        let mut _sg = 0;
        while _sg < 21usize {
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
            let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(8usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(0usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(8usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(1usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(8usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(2usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(72usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(3usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(72usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(4usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(8usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(5usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(8usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(7usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(9usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(0usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(9usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(1usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(9usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(2usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(73usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(3usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(73usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(4usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(9usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(5usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(9usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(7usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(10usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(0usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(10usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(1usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(10usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(2usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(74usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(3usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(74usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(4usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(10usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(5usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(10usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(7usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(11usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(0usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(11usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(1usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(11usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(2usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(75usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(3usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(75usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(4usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(11usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(5usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(11usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(7usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(12usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(0usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(12usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(1usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(12usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(2usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(76usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(3usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(76usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(4usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(12usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(5usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(12usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(7usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(13usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(0usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(13usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(1usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(13usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(2usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(77usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(3usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(77usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(4usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(13usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(5usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(13usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(7usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(14usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(0usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(14usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(1usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(14usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(2usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(78usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(3usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(78usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(4usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(14usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(5usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(14usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(7usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(15usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(0usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(15usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(1usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(15usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(2usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(79usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(3usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(79usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(4usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(15usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(5usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(15usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(7usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(16usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(0usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(16usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(1usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(16usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(2usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(80usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(3usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(80usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(4usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(16usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(5usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(16usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(7usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(17usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(0usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(17usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(1usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(17usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(2usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(81usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(3usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(81usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(4usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(17usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(5usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(17usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(7usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(18usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(0usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(18usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(1usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(18usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(2usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(82usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(3usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(82usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(4usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(18usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(5usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(18usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(7usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(19usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(0usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(19usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(1usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(19usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(2usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(83usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(3usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(83usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(4usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(19usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(5usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(19usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(7usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(20usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(0usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(20usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(1usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(20usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(2usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(84usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(3usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(84usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(4usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(20usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(5usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(20usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(7usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(21usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(0usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(21usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(1usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(21usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(2usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(85usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(3usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(85usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(4usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(21usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(5usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(21usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(7usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(22usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(0usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(22usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(1usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(22usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(2usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(86usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(3usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(86usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(4usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(22usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(5usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(22usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(7usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(23usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(0usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(23usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(1usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(23usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(2usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(87usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(3usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(87usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(4usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(23usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(5usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(23usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(7usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(88usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(89usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(90usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(91usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(92usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(93usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(94usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(95usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(96usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(97usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(98usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(99usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(100usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(101usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(102usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(103usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(3usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            {
                let mut inner = BabyBearExt4::ZERO;
                let mut t = unsafe { evals.get_unchecked(8usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(9usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(10usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(11usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(12usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(13usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(14usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(15usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(16usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(17usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(18usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(19usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(20usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(21usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(22usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let mut t = unsafe { evals.get_unchecked(23usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut inner, &t);
                let a_val = unsafe { evals.get_unchecked(5usize) }[j];
                field_ops::mul_assign(&mut inner, &a_val);
                field_ops::add_assign(&mut val, &inner);
            }
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        const SIMPLE_GATES: [(usize, [usize; 4]); 63usize] = [
            (1usize, [135usize, 0usize, 0usize, 0usize]),
            (1usize, [136usize, 0usize, 0usize, 0usize]),
            (6usize, [88usize, 158usize, 215usize, 0usize]),
            (5usize, [89usize, 90usize, 0usize, 0usize]),
            (5usize, [91usize, 92usize, 0usize, 0usize]),
            (5usize, [93usize, 94usize, 0usize, 0usize]),
            (5usize, [95usize, 96usize, 0usize, 0usize]),
            (5usize, [97usize, 98usize, 0usize, 0usize]),
            (5usize, [99usize, 100usize, 0usize, 0usize]),
            (5usize, [101usize, 102usize, 0usize, 0usize]),
            (1usize, [103usize, 0usize, 0usize, 0usize]),
            (6usize, [213usize, 159usize, 216usize, 0usize]),
            (5usize, [214usize, 257usize, 0usize, 0usize]),
            (5usize, [258usize, 259usize, 0usize, 0usize]),
            (5usize, [260usize, 261usize, 0usize, 0usize]),
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
            (5usize, [288usize, 289usize, 0usize, 0usize]),
            (5usize, [290usize, 291usize, 0usize, 0usize]),
            (5usize, [292usize, 293usize, 0usize, 0usize]),
            (1usize, [294usize, 0usize, 0usize, 0usize]),
            (6usize, [295usize, 160usize, 296usize, 0usize]),
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
            (5usize, [331usize, 332usize, 0usize, 0usize]),
            (5usize, [333usize, 334usize, 0usize, 0usize]),
            (5usize, [335usize, 336usize, 0usize, 0usize]),
            (5usize, [337usize, 338usize, 0usize, 0usize]),
            (5usize, [339usize, 340usize, 0usize, 0usize]),
            (5usize, [341usize, 342usize, 0usize, 0usize]),
            (5usize, [343usize, 344usize, 0usize, 0usize]),
            (5usize, [345usize, 346usize, 0usize, 0usize]),
            (5usize, [347usize, 348usize, 0usize, 0usize]),
            (5usize, [349usize, 350usize, 0usize, 0usize]),
            (5usize, [351usize, 352usize, 0usize, 0usize]),
            (5usize, [353usize, 354usize, 0usize, 0usize]),
            (5usize, [355usize, 356usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 63usize {
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
                    const CK_LIN: [(u32, usize, usize); 208usize] = [
                        (268435454u32, 1usize, 0usize),
                        (1744830467u32, 2usize, 0usize),
                        (1744830467u32, 71usize, 0usize),
                        (536870908u32, 1usize, 1usize),
                        (1744830467u32, 2usize, 1usize),
                        (1744830467u32, 72usize, 1usize),
                        (1073741816u32, 1usize, 2usize),
                        (1744830467u32, 2usize, 2usize),
                        (1744830467u32, 73usize, 2usize),
                        (134217711u32, 1usize, 3usize),
                        (1744830467u32, 2usize, 3usize),
                        (268435454u32, 69usize, 3usize),
                        (1744830467u32, 74usize, 3usize),
                        (268435422u32, 1usize, 4usize),
                        (1744830467u32, 2usize, 4usize),
                        (1744830467u32, 75usize, 4usize),
                        (536870844u32, 1usize, 5usize),
                        (1744830467u32, 2usize, 5usize),
                        (1744830467u32, 76usize, 5usize),
                        (1073741688u32, 1usize, 6usize),
                        (1744830467u32, 77usize, 6usize),
                        (134217455u32, 1usize, 7usize),
                        (1744830467u32, 2usize, 7usize),
                        (1744830467u32, 78usize, 7usize),
                        (1744970275u32, 3usize, 24usize),
                        (268435454u32, 4usize, 24usize),
                        (1744830467u32, 79usize, 24usize),
                        (1744970275u32, 4usize, 25usize),
                        (268435454u32, 5usize, 25usize),
                        (1744830467u32, 80usize, 25usize),
                        (1744970275u32, 5usize, 26usize),
                        (268435454u32, 6usize, 26usize),
                        (1744830467u32, 81usize, 26usize),
                        (1744970275u32, 6usize, 27usize),
                        (268435454u32, 7usize, 27usize),
                        (1744830467u32, 82usize, 27usize),
                        (1744970275u32, 7usize, 28usize),
                        (268435454u32, 8usize, 28usize),
                        (1744830467u32, 83usize, 28usize),
                        (1744970275u32, 8usize, 29usize),
                        (268435454u32, 9usize, 29usize),
                        (1744830467u32, 84usize, 29usize),
                        (1744970275u32, 9usize, 30usize),
                        (268435454u32, 10usize, 30usize),
                        (1744830467u32, 85usize, 30usize),
                        (1744970275u32, 10usize, 31usize),
                        (268435454u32, 11usize, 31usize),
                        (1744830467u32, 86usize, 31usize),
                        (1744970275u32, 11usize, 32usize),
                        (268435454u32, 12usize, 32usize),
                        (1744830467u32, 87usize, 32usize),
                        (1744970275u32, 12usize, 33usize),
                        (268435454u32, 13usize, 33usize),
                        (1744830467u32, 88usize, 33usize),
                        (1744970275u32, 13usize, 34usize),
                        (268435454u32, 14usize, 34usize),
                        (1744830467u32, 89usize, 34usize),
                        (1744970275u32, 14usize, 35usize),
                        (268435454u32, 15usize, 35usize),
                        (1744830467u32, 90usize, 35usize),
                        (1744970275u32, 15usize, 36usize),
                        (268435454u32, 16usize, 36usize),
                        (1744830467u32, 91usize, 36usize),
                        (1744970275u32, 16usize, 37usize),
                        (268435454u32, 17usize, 37usize),
                        (1744830467u32, 92usize, 37usize),
                        (1744970275u32, 17usize, 38usize),
                        (268435454u32, 18usize, 38usize),
                        (1744830467u32, 93usize, 38usize),
                        (1744970275u32, 18usize, 39usize),
                        (1744830467u32, 94usize, 39usize),
                        (2013200385u32, 20usize, 72usize),
                        (2013200385u32, 21usize, 73usize),
                        (2013200385u32, 22usize, 74usize),
                        (2013200385u32, 23usize, 75usize),
                        (2013200385u32, 24usize, 76usize),
                        (2013200385u32, 25usize, 77usize),
                        (2013200385u32, 26usize, 78usize),
                        (2013200385u32, 27usize, 79usize),
                        (2013200385u32, 28usize, 80usize),
                        (2013200385u32, 29usize, 81usize),
                        (2013200385u32, 30usize, 82usize),
                        (2013200385u32, 31usize, 83usize),
                        (2013200385u32, 32usize, 84usize),
                        (2013200385u32, 33usize, 85usize),
                        (2013200385u32, 34usize, 86usize),
                        (2013200385u32, 35usize, 87usize),
                        (2013200385u32, 36usize, 88usize),
                        (2013200385u32, 37usize, 89usize),
                        (2013200385u32, 38usize, 90usize),
                        (2013200385u32, 39usize, 91usize),
                        (2013200385u32, 40usize, 92usize),
                        (2013200385u32, 41usize, 93usize),
                        (2013200385u32, 42usize, 94usize),
                        (2013200385u32, 43usize, 95usize),
                        (2013200385u32, 44usize, 96usize),
                        (2013200385u32, 45usize, 97usize),
                        (2013200385u32, 46usize, 98usize),
                        (2013200385u32, 47usize, 99usize),
                        (2013200385u32, 48usize, 100usize),
                        (2013200385u32, 49usize, 101usize),
                        (2013200385u32, 50usize, 102usize),
                        (1744830467u32, 50usize, 103usize),
                        (1744830467u32, 19usize, 104usize),
                        (65536u32, 20usize, 104usize),
                        (1744830467u32, 20usize, 105usize),
                        (65536u32, 21usize, 105usize),
                        (1744830467u32, 21usize, 106usize),
                        (65536u32, 22usize, 106usize),
                        (1744830467u32, 22usize, 107usize),
                        (65536u32, 23usize, 107usize),
                        (1744830467u32, 23usize, 108usize),
                        (65536u32, 24usize, 108usize),
                        (1744830467u32, 24usize, 109usize),
                        (65536u32, 25usize, 109usize),
                        (1744830467u32, 25usize, 110usize),
                        (65536u32, 26usize, 110usize),
                        (1744830467u32, 26usize, 111usize),
                        (65536u32, 27usize, 111usize),
                        (1744830467u32, 27usize, 112usize),
                        (65536u32, 28usize, 112usize),
                        (1744830467u32, 28usize, 113usize),
                        (65536u32, 29usize, 113usize),
                        (1744830467u32, 29usize, 114usize),
                        (65536u32, 30usize, 114usize),
                        (1744830467u32, 30usize, 115usize),
                        (65536u32, 31usize, 115usize),
                        (1744830467u32, 31usize, 116usize),
                        (65536u32, 32usize, 116usize),
                        (1744830467u32, 32usize, 117usize),
                        (65536u32, 33usize, 117usize),
                        (1744830467u32, 33usize, 118usize),
                        (65536u32, 34usize, 118usize),
                        (1744830467u32, 34usize, 119usize),
                        (65536u32, 35usize, 119usize),
                        (1744830467u32, 35usize, 120usize),
                        (65536u32, 36usize, 120usize),
                        (1744830467u32, 36usize, 121usize),
                        (65536u32, 37usize, 121usize),
                        (1744830467u32, 37usize, 122usize),
                        (65536u32, 38usize, 122usize),
                        (1744830467u32, 38usize, 123usize),
                        (65536u32, 39usize, 123usize),
                        (1744830467u32, 39usize, 124usize),
                        (65536u32, 40usize, 124usize),
                        (1744830467u32, 40usize, 125usize),
                        (65536u32, 41usize, 125usize),
                        (1744830467u32, 41usize, 126usize),
                        (65536u32, 42usize, 126usize),
                        (1744830467u32, 42usize, 127usize),
                        (65536u32, 43usize, 127usize),
                        (1744830467u32, 43usize, 128usize),
                        (65536u32, 44usize, 128usize),
                        (1744830467u32, 44usize, 129usize),
                        (65536u32, 45usize, 129usize),
                        (1744830467u32, 45usize, 130usize),
                        (65536u32, 46usize, 130usize),
                        (1744830467u32, 46usize, 131usize),
                        (65536u32, 47usize, 131usize),
                        (1744830467u32, 47usize, 132usize),
                        (65536u32, 48usize, 132usize),
                        (1744830467u32, 48usize, 133usize),
                        (65536u32, 49usize, 133usize),
                        (1744830467u32, 49usize, 134usize),
                        (65536u32, 50usize, 134usize),
                        (268435454u32, 67usize, 136usize),
                        (1744830467u32, 95usize, 136usize),
                        (1744830467u32, 67usize, 137usize),
                        (1744830467u32, 68usize, 138usize),
                        (1744830467u32, 96usize, 139usize),
                        (1744830467u32, 97usize, 140usize),
                        (1744830467u32, 98usize, 141usize),
                        (1744830467u32, 99usize, 142usize),
                        (1744830467u32, 100usize, 143usize),
                        (1744830467u32, 101usize, 144usize),
                        (1744830467u32, 102usize, 145usize),
                        (1744830467u32, 103usize, 146usize),
                        (1744830467u32, 104usize, 147usize),
                        (1744830467u32, 105usize, 148usize),
                        (1744830467u32, 106usize, 149usize),
                        (1744830467u32, 107usize, 150usize),
                        (1744830467u32, 108usize, 151usize),
                        (1744830467u32, 109usize, 152usize),
                        (1744830467u32, 110usize, 153usize),
                        (1744830467u32, 111usize, 154usize),
                        (1744830467u32, 112usize, 155usize),
                        (1744830467u32, 113usize, 156usize),
                        (1744830467u32, 114usize, 157usize),
                        (1744830467u32, 51usize, 163usize),
                        (1744830467u32, 52usize, 164usize),
                        (1744830467u32, 53usize, 167usize),
                        (1744830467u32, 54usize, 168usize),
                        (1744830467u32, 55usize, 171usize),
                        (1744830467u32, 56usize, 172usize),
                        (1744830467u32, 57usize, 175usize),
                        (1744830467u32, 58usize, 176usize),
                        (1744830467u32, 59usize, 179usize),
                        (1744830467u32, 60usize, 180usize),
                        (1744830467u32, 61usize, 183usize),
                        (1744830467u32, 62usize, 184usize),
                        (1744830467u32, 63usize, 187usize),
                        (1744830467u32, 64usize, 188usize),
                        (1744830467u32, 65usize, 191usize),
                        (1744830467u32, 66usize, 192usize),
                        (1744830467u32, 1usize, 209usize),
                        (1744830467u32, 69usize, 210usize),
                        (268435454u32, 70usize, 211usize),
                        (1744830467u32, 0usize, 212usize),
                    ];
                    let mut _i: usize = 0;
                    while _i < 208usize {
                        let (coeff, pow, eval_idx) = CK_LIN[_i];
                        let val = evals.get_unchecked(eval_idx)[j];
                        let mut t: BabyBearExt4 = *challenge_powers.get_unchecked(pow);
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(coeff),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                        _i += 1;
                    }
                }
                {
                    const CK_QUAD_GROUPS: [(usize, usize, usize, usize); 1358usize] = [
                        (0usize, 0usize, 0usize, 2usize),
                        (0usize, 1usize, 2usize, 1usize),
                        (0usize, 2usize, 3usize, 1usize),
                        (0usize, 3usize, 4usize, 1usize),
                        (0usize, 4usize, 5usize, 1usize),
                        (0usize, 5usize, 6usize, 1usize),
                        (0usize, 6usize, 7usize, 1usize),
                        (0usize, 7usize, 8usize, 1usize),
                        (0usize, 8usize, 9usize, 2usize),
                        (0usize, 9usize, 11usize, 2usize),
                        (0usize, 10usize, 13usize, 2usize),
                        (0usize, 11usize, 15usize, 2usize),
                        (0usize, 12usize, 17usize, 2usize),
                        (0usize, 13usize, 19usize, 2usize),
                        (0usize, 14usize, 21usize, 2usize),
                        (0usize, 15usize, 23usize, 2usize),
                        (0usize, 16usize, 25usize, 2usize),
                        (0usize, 17usize, 27usize, 2usize),
                        (0usize, 18usize, 29usize, 2usize),
                        (0usize, 19usize, 31usize, 2usize),
                        (0usize, 20usize, 33usize, 2usize),
                        (0usize, 21usize, 35usize, 2usize),
                        (0usize, 22usize, 37usize, 2usize),
                        (0usize, 23usize, 39usize, 2usize),
                        (0usize, 39usize, 41usize, 1usize),
                        (1usize, 1usize, 42usize, 2usize),
                        (1usize, 2usize, 44usize, 1usize),
                        (1usize, 3usize, 45usize, 1usize),
                        (1usize, 4usize, 46usize, 1usize),
                        (1usize, 5usize, 47usize, 1usize),
                        (1usize, 6usize, 48usize, 1usize),
                        (1usize, 7usize, 49usize, 1usize),
                        (1usize, 8usize, 50usize, 2usize),
                        (1usize, 9usize, 52usize, 2usize),
                        (1usize, 10usize, 54usize, 2usize),
                        (1usize, 11usize, 56usize, 2usize),
                        (1usize, 12usize, 58usize, 2usize),
                        (1usize, 13usize, 60usize, 2usize),
                        (1usize, 14usize, 62usize, 2usize),
                        (1usize, 15usize, 64usize, 2usize),
                        (1usize, 16usize, 66usize, 2usize),
                        (1usize, 17usize, 68usize, 2usize),
                        (1usize, 18usize, 70usize, 2usize),
                        (1usize, 19usize, 72usize, 2usize),
                        (1usize, 20usize, 74usize, 2usize),
                        (1usize, 21usize, 76usize, 2usize),
                        (1usize, 22usize, 78usize, 2usize),
                        (1usize, 23usize, 80usize, 2usize),
                        (1usize, 39usize, 82usize, 1usize),
                        (2usize, 2usize, 83usize, 2usize),
                        (2usize, 3usize, 85usize, 1usize),
                        (2usize, 4usize, 86usize, 1usize),
                        (2usize, 5usize, 87usize, 1usize),
                        (2usize, 6usize, 88usize, 1usize),
                        (2usize, 7usize, 89usize, 1usize),
                        (2usize, 8usize, 90usize, 2usize),
                        (2usize, 9usize, 92usize, 2usize),
                        (2usize, 10usize, 94usize, 2usize),
                        (2usize, 11usize, 96usize, 2usize),
                        (2usize, 12usize, 98usize, 2usize),
                        (2usize, 13usize, 100usize, 2usize),
                        (2usize, 14usize, 102usize, 2usize),
                        (2usize, 15usize, 104usize, 2usize),
                        (2usize, 16usize, 106usize, 2usize),
                        (2usize, 17usize, 108usize, 2usize),
                        (2usize, 18usize, 110usize, 2usize),
                        (2usize, 19usize, 112usize, 2usize),
                        (2usize, 20usize, 114usize, 2usize),
                        (2usize, 21usize, 116usize, 2usize),
                        (2usize, 22usize, 118usize, 2usize),
                        (2usize, 23usize, 120usize, 2usize),
                        (2usize, 39usize, 122usize, 1usize),
                        (3usize, 3usize, 123usize, 2usize),
                        (3usize, 4usize, 125usize, 1usize),
                        (3usize, 5usize, 126usize, 1usize),
                        (3usize, 7usize, 127usize, 1usize),
                        (3usize, 72usize, 128usize, 1usize),
                        (3usize, 73usize, 129usize, 1usize),
                        (3usize, 74usize, 130usize, 1usize),
                        (3usize, 75usize, 131usize, 1usize),
                        (3usize, 76usize, 132usize, 1usize),
                        (3usize, 77usize, 133usize, 1usize),
                        (3usize, 78usize, 134usize, 1usize),
                        (3usize, 79usize, 135usize, 1usize),
                        (3usize, 80usize, 136usize, 1usize),
                        (3usize, 81usize, 137usize, 1usize),
                        (3usize, 82usize, 138usize, 1usize),
                        (3usize, 83usize, 139usize, 1usize),
                        (3usize, 84usize, 140usize, 1usize),
                        (3usize, 85usize, 141usize, 1usize),
                        (3usize, 86usize, 142usize, 1usize),
                        (3usize, 87usize, 143usize, 1usize),
                        (3usize, 136usize, 144usize, 1usize),
                        (4usize, 4usize, 145usize, 2usize),
                        (4usize, 5usize, 147usize, 1usize),
                        (4usize, 7usize, 148usize, 1usize),
                        (4usize, 88usize, 149usize, 1usize),
                        (4usize, 89usize, 150usize, 1usize),
                        (4usize, 90usize, 151usize, 1usize),
                        (4usize, 91usize, 152usize, 1usize),
                        (4usize, 92usize, 153usize, 1usize),
                        (4usize, 93usize, 154usize, 1usize),
                        (4usize, 94usize, 155usize, 1usize),
                        (4usize, 95usize, 156usize, 1usize),
                        (4usize, 96usize, 157usize, 1usize),
                        (4usize, 97usize, 158usize, 1usize),
                        (4usize, 98usize, 159usize, 1usize),
                        (4usize, 99usize, 160usize, 1usize),
                        (4usize, 100usize, 161usize, 1usize),
                        (4usize, 101usize, 162usize, 1usize),
                        (4usize, 102usize, 163usize, 1usize),
                        (4usize, 103usize, 164usize, 1usize),
                        (5usize, 5usize, 165usize, 2usize),
                        (5usize, 7usize, 167usize, 1usize),
                        (5usize, 8usize, 168usize, 1usize),
                        (5usize, 9usize, 169usize, 1usize),
                        (5usize, 10usize, 170usize, 1usize),
                        (5usize, 11usize, 171usize, 1usize),
                        (5usize, 12usize, 172usize, 1usize),
                        (5usize, 13usize, 173usize, 1usize),
                        (5usize, 14usize, 174usize, 1usize),
                        (5usize, 15usize, 175usize, 1usize),
                        (5usize, 16usize, 176usize, 1usize),
                        (5usize, 17usize, 177usize, 1usize),
                        (5usize, 18usize, 178usize, 1usize),
                        (5usize, 19usize, 179usize, 1usize),
                        (5usize, 20usize, 180usize, 1usize),
                        (5usize, 21usize, 181usize, 1usize),
                        (5usize, 22usize, 182usize, 1usize),
                        (5usize, 23usize, 183usize, 1usize),
                        (5usize, 137usize, 184usize, 1usize),
                        (5usize, 138usize, 185usize, 1usize),
                        (6usize, 6usize, 186usize, 1usize),
                        (6usize, 7usize, 187usize, 1usize),
                        (7usize, 7usize, 188usize, 2usize),
                        (7usize, 8usize, 190usize, 2usize),
                        (7usize, 9usize, 192usize, 2usize),
                        (7usize, 10usize, 194usize, 2usize),
                        (7usize, 11usize, 196usize, 2usize),
                        (7usize, 12usize, 198usize, 2usize),
                        (7usize, 13usize, 200usize, 2usize),
                        (7usize, 14usize, 202usize, 2usize),
                        (7usize, 15usize, 204usize, 2usize),
                        (7usize, 16usize, 206usize, 2usize),
                        (7usize, 17usize, 208usize, 2usize),
                        (7usize, 18usize, 210usize, 2usize),
                        (7usize, 19usize, 212usize, 2usize),
                        (7usize, 20usize, 214usize, 2usize),
                        (7usize, 21usize, 216usize, 2usize),
                        (7usize, 22usize, 218usize, 2usize),
                        (7usize, 23usize, 220usize, 2usize),
                        (7usize, 39usize, 222usize, 1usize),
                        (24usize, 24usize, 223usize, 1usize),
                        (25usize, 25usize, 224usize, 1usize),
                        (26usize, 26usize, 225usize, 1usize),
                        (27usize, 27usize, 226usize, 1usize),
                        (28usize, 28usize, 227usize, 1usize),
                        (29usize, 29usize, 228usize, 1usize),
                        (30usize, 30usize, 229usize, 1usize),
                        (31usize, 31usize, 230usize, 1usize),
                        (32usize, 32usize, 231usize, 1usize),
                        (33usize, 33usize, 232usize, 1usize),
                        (34usize, 34usize, 233usize, 1usize),
                        (35usize, 35usize, 234usize, 1usize),
                        (36usize, 36usize, 235usize, 1usize),
                        (37usize, 37usize, 236usize, 1usize),
                        (38usize, 38usize, 237usize, 1usize),
                        (39usize, 39usize, 238usize, 1usize),
                        (39usize, 136usize, 239usize, 1usize),
                        (40usize, 56usize, 240usize, 2usize),
                        (40usize, 57usize, 242usize, 2usize),
                        (40usize, 58usize, 244usize, 2usize),
                        (40usize, 59usize, 246usize, 2usize),
                        (40usize, 60usize, 248usize, 2usize),
                        (40usize, 61usize, 250usize, 2usize),
                        (40usize, 62usize, 252usize, 2usize),
                        (40usize, 63usize, 254usize, 2usize),
                        (40usize, 64usize, 256usize, 2usize),
                        (40usize, 65usize, 258usize, 2usize),
                        (40usize, 66usize, 260usize, 2usize),
                        (40usize, 67usize, 262usize, 2usize),
                        (40usize, 68usize, 264usize, 2usize),
                        (40usize, 69usize, 266usize, 2usize),
                        (40usize, 70usize, 268usize, 2usize),
                        (40usize, 71usize, 270usize, 2usize),
                        (41usize, 56usize, 272usize, 2usize),
                        (41usize, 57usize, 274usize, 2usize),
                        (41usize, 58usize, 276usize, 2usize),
                        (41usize, 59usize, 278usize, 2usize),
                        (41usize, 60usize, 280usize, 2usize),
                        (41usize, 61usize, 282usize, 2usize),
                        (41usize, 62usize, 284usize, 2usize),
                        (41usize, 63usize, 286usize, 2usize),
                        (41usize, 64usize, 288usize, 2usize),
                        (41usize, 65usize, 290usize, 2usize),
                        (41usize, 66usize, 292usize, 2usize),
                        (41usize, 67usize, 294usize, 2usize),
                        (41usize, 68usize, 296usize, 2usize),
                        (41usize, 69usize, 298usize, 2usize),
                        (41usize, 70usize, 300usize, 2usize),
                        (41usize, 71usize, 302usize, 2usize),
                        (42usize, 56usize, 304usize, 2usize),
                        (42usize, 57usize, 306usize, 2usize),
                        (42usize, 58usize, 308usize, 2usize),
                        (42usize, 59usize, 310usize, 2usize),
                        (42usize, 60usize, 312usize, 2usize),
                        (42usize, 61usize, 314usize, 2usize),
                        (42usize, 62usize, 316usize, 2usize),
                        (42usize, 63usize, 318usize, 2usize),
                        (42usize, 64usize, 320usize, 2usize),
                        (42usize, 65usize, 322usize, 2usize),
                        (42usize, 66usize, 324usize, 2usize),
                        (42usize, 67usize, 326usize, 2usize),
                        (42usize, 68usize, 328usize, 2usize),
                        (42usize, 69usize, 330usize, 2usize),
                        (42usize, 70usize, 332usize, 2usize),
                        (42usize, 71usize, 334usize, 2usize),
                        (43usize, 56usize, 336usize, 2usize),
                        (43usize, 57usize, 338usize, 2usize),
                        (43usize, 58usize, 340usize, 2usize),
                        (43usize, 59usize, 342usize, 2usize),
                        (43usize, 60usize, 344usize, 2usize),
                        (43usize, 61usize, 346usize, 2usize),
                        (43usize, 62usize, 348usize, 2usize),
                        (43usize, 63usize, 350usize, 2usize),
                        (43usize, 64usize, 352usize, 2usize),
                        (43usize, 65usize, 354usize, 2usize),
                        (43usize, 66usize, 356usize, 2usize),
                        (43usize, 67usize, 358usize, 2usize),
                        (43usize, 68usize, 360usize, 2usize),
                        (43usize, 69usize, 362usize, 2usize),
                        (43usize, 70usize, 364usize, 2usize),
                        (43usize, 71usize, 366usize, 2usize),
                        (44usize, 56usize, 368usize, 2usize),
                        (44usize, 57usize, 370usize, 2usize),
                        (44usize, 58usize, 372usize, 2usize),
                        (44usize, 59usize, 374usize, 2usize),
                        (44usize, 60usize, 376usize, 2usize),
                        (44usize, 61usize, 378usize, 2usize),
                        (44usize, 62usize, 380usize, 2usize),
                        (44usize, 63usize, 382usize, 2usize),
                        (44usize, 64usize, 384usize, 2usize),
                        (44usize, 65usize, 386usize, 2usize),
                        (44usize, 66usize, 388usize, 2usize),
                        (44usize, 67usize, 390usize, 2usize),
                        (44usize, 68usize, 392usize, 2usize),
                        (44usize, 69usize, 394usize, 2usize),
                        (44usize, 70usize, 396usize, 2usize),
                        (44usize, 71usize, 398usize, 2usize),
                        (45usize, 56usize, 400usize, 2usize),
                        (45usize, 57usize, 402usize, 2usize),
                        (45usize, 58usize, 404usize, 2usize),
                        (45usize, 59usize, 406usize, 2usize),
                        (45usize, 60usize, 408usize, 2usize),
                        (45usize, 61usize, 410usize, 2usize),
                        (45usize, 62usize, 412usize, 2usize),
                        (45usize, 63usize, 414usize, 2usize),
                        (45usize, 64usize, 416usize, 2usize),
                        (45usize, 65usize, 418usize, 2usize),
                        (45usize, 66usize, 420usize, 2usize),
                        (45usize, 67usize, 422usize, 2usize),
                        (45usize, 68usize, 424usize, 2usize),
                        (45usize, 69usize, 426usize, 2usize),
                        (45usize, 70usize, 428usize, 2usize),
                        (45usize, 71usize, 430usize, 2usize),
                        (46usize, 56usize, 432usize, 2usize),
                        (46usize, 57usize, 434usize, 2usize),
                        (46usize, 58usize, 436usize, 2usize),
                        (46usize, 59usize, 438usize, 2usize),
                        (46usize, 60usize, 440usize, 2usize),
                        (46usize, 61usize, 442usize, 2usize),
                        (46usize, 62usize, 444usize, 2usize),
                        (46usize, 63usize, 446usize, 2usize),
                        (46usize, 64usize, 448usize, 2usize),
                        (46usize, 65usize, 450usize, 2usize),
                        (46usize, 66usize, 452usize, 2usize),
                        (46usize, 67usize, 454usize, 2usize),
                        (46usize, 68usize, 456usize, 2usize),
                        (46usize, 69usize, 458usize, 2usize),
                        (46usize, 70usize, 460usize, 2usize),
                        (46usize, 71usize, 462usize, 2usize),
                        (47usize, 56usize, 464usize, 2usize),
                        (47usize, 57usize, 466usize, 2usize),
                        (47usize, 58usize, 468usize, 2usize),
                        (47usize, 59usize, 470usize, 2usize),
                        (47usize, 60usize, 472usize, 2usize),
                        (47usize, 61usize, 474usize, 2usize),
                        (47usize, 62usize, 476usize, 2usize),
                        (47usize, 63usize, 478usize, 2usize),
                        (47usize, 64usize, 480usize, 2usize),
                        (47usize, 65usize, 482usize, 2usize),
                        (47usize, 66usize, 484usize, 2usize),
                        (47usize, 67usize, 486usize, 2usize),
                        (47usize, 68usize, 488usize, 2usize),
                        (47usize, 69usize, 490usize, 2usize),
                        (47usize, 70usize, 492usize, 2usize),
                        (47usize, 71usize, 494usize, 2usize),
                        (48usize, 56usize, 496usize, 2usize),
                        (48usize, 57usize, 498usize, 2usize),
                        (48usize, 58usize, 500usize, 2usize),
                        (48usize, 59usize, 502usize, 2usize),
                        (48usize, 60usize, 504usize, 2usize),
                        (48usize, 61usize, 506usize, 2usize),
                        (48usize, 62usize, 508usize, 2usize),
                        (48usize, 63usize, 510usize, 2usize),
                        (48usize, 64usize, 512usize, 2usize),
                        (48usize, 65usize, 514usize, 2usize),
                        (48usize, 66usize, 516usize, 2usize),
                        (48usize, 67usize, 518usize, 2usize),
                        (48usize, 68usize, 520usize, 2usize),
                        (48usize, 69usize, 522usize, 2usize),
                        (48usize, 70usize, 524usize, 2usize),
                        (48usize, 71usize, 526usize, 2usize),
                        (49usize, 56usize, 528usize, 2usize),
                        (49usize, 57usize, 530usize, 2usize),
                        (49usize, 58usize, 532usize, 2usize),
                        (49usize, 59usize, 534usize, 2usize),
                        (49usize, 60usize, 536usize, 2usize),
                        (49usize, 61usize, 538usize, 2usize),
                        (49usize, 62usize, 540usize, 2usize),
                        (49usize, 63usize, 542usize, 2usize),
                        (49usize, 64usize, 544usize, 2usize),
                        (49usize, 65usize, 546usize, 2usize),
                        (49usize, 66usize, 548usize, 2usize),
                        (49usize, 67usize, 550usize, 2usize),
                        (49usize, 68usize, 552usize, 2usize),
                        (49usize, 69usize, 554usize, 2usize),
                        (49usize, 70usize, 556usize, 2usize),
                        (49usize, 71usize, 558usize, 2usize),
                        (50usize, 56usize, 560usize, 2usize),
                        (50usize, 57usize, 562usize, 2usize),
                        (50usize, 58usize, 564usize, 2usize),
                        (50usize, 59usize, 566usize, 2usize),
                        (50usize, 60usize, 568usize, 2usize),
                        (50usize, 61usize, 570usize, 2usize),
                        (50usize, 62usize, 572usize, 2usize),
                        (50usize, 63usize, 574usize, 2usize),
                        (50usize, 64usize, 576usize, 2usize),
                        (50usize, 65usize, 578usize, 2usize),
                        (50usize, 66usize, 580usize, 2usize),
                        (50usize, 67usize, 582usize, 2usize),
                        (50usize, 68usize, 584usize, 2usize),
                        (50usize, 69usize, 586usize, 2usize),
                        (50usize, 70usize, 588usize, 2usize),
                        (50usize, 71usize, 590usize, 2usize),
                        (51usize, 56usize, 592usize, 2usize),
                        (51usize, 57usize, 594usize, 2usize),
                        (51usize, 58usize, 596usize, 2usize),
                        (51usize, 59usize, 598usize, 2usize),
                        (51usize, 60usize, 600usize, 2usize),
                        (51usize, 61usize, 602usize, 2usize),
                        (51usize, 62usize, 604usize, 2usize),
                        (51usize, 63usize, 606usize, 2usize),
                        (51usize, 64usize, 608usize, 2usize),
                        (51usize, 65usize, 610usize, 2usize),
                        (51usize, 66usize, 612usize, 2usize),
                        (51usize, 67usize, 614usize, 2usize),
                        (51usize, 68usize, 616usize, 2usize),
                        (51usize, 69usize, 618usize, 2usize),
                        (51usize, 70usize, 620usize, 2usize),
                        (51usize, 71usize, 622usize, 2usize),
                        (52usize, 56usize, 624usize, 2usize),
                        (52usize, 57usize, 626usize, 2usize),
                        (52usize, 58usize, 628usize, 2usize),
                        (52usize, 59usize, 630usize, 2usize),
                        (52usize, 60usize, 632usize, 2usize),
                        (52usize, 61usize, 634usize, 2usize),
                        (52usize, 62usize, 636usize, 2usize),
                        (52usize, 63usize, 638usize, 2usize),
                        (52usize, 64usize, 640usize, 2usize),
                        (52usize, 65usize, 642usize, 2usize),
                        (52usize, 66usize, 644usize, 2usize),
                        (52usize, 67usize, 646usize, 2usize),
                        (52usize, 68usize, 648usize, 2usize),
                        (52usize, 69usize, 650usize, 2usize),
                        (52usize, 70usize, 652usize, 2usize),
                        (52usize, 71usize, 654usize, 2usize),
                        (53usize, 56usize, 656usize, 2usize),
                        (53usize, 57usize, 658usize, 2usize),
                        (53usize, 58usize, 660usize, 2usize),
                        (53usize, 59usize, 662usize, 2usize),
                        (53usize, 60usize, 664usize, 2usize),
                        (53usize, 61usize, 666usize, 2usize),
                        (53usize, 62usize, 668usize, 2usize),
                        (53usize, 63usize, 670usize, 2usize),
                        (53usize, 64usize, 672usize, 2usize),
                        (53usize, 65usize, 674usize, 2usize),
                        (53usize, 66usize, 676usize, 2usize),
                        (53usize, 67usize, 678usize, 2usize),
                        (53usize, 68usize, 680usize, 2usize),
                        (53usize, 69usize, 682usize, 2usize),
                        (53usize, 70usize, 684usize, 2usize),
                        (53usize, 71usize, 686usize, 2usize),
                        (54usize, 56usize, 688usize, 2usize),
                        (54usize, 57usize, 690usize, 2usize),
                        (54usize, 58usize, 692usize, 2usize),
                        (54usize, 59usize, 694usize, 2usize),
                        (54usize, 60usize, 696usize, 2usize),
                        (54usize, 61usize, 698usize, 2usize),
                        (54usize, 62usize, 700usize, 2usize),
                        (54usize, 63usize, 702usize, 2usize),
                        (54usize, 64usize, 704usize, 2usize),
                        (54usize, 65usize, 706usize, 2usize),
                        (54usize, 66usize, 708usize, 2usize),
                        (54usize, 67usize, 710usize, 2usize),
                        (54usize, 68usize, 712usize, 2usize),
                        (54usize, 69usize, 714usize, 2usize),
                        (54usize, 70usize, 716usize, 2usize),
                        (54usize, 71usize, 718usize, 2usize),
                        (55usize, 56usize, 720usize, 2usize),
                        (55usize, 57usize, 722usize, 2usize),
                        (55usize, 58usize, 724usize, 2usize),
                        (55usize, 59usize, 726usize, 2usize),
                        (55usize, 60usize, 728usize, 2usize),
                        (55usize, 61usize, 730usize, 2usize),
                        (55usize, 62usize, 732usize, 2usize),
                        (55usize, 63usize, 734usize, 2usize),
                        (55usize, 64usize, 736usize, 2usize),
                        (55usize, 65usize, 738usize, 2usize),
                        (55usize, 66usize, 740usize, 2usize),
                        (55usize, 67usize, 742usize, 2usize),
                        (55usize, 68usize, 744usize, 2usize),
                        (55usize, 69usize, 746usize, 2usize),
                        (55usize, 70usize, 748usize, 2usize),
                        (55usize, 71usize, 750usize, 2usize),
                        (136usize, 136usize, 752usize, 1usize),
                        (139usize, 139usize, 753usize, 1usize),
                        (140usize, 140usize, 754usize, 1usize),
                        (141usize, 141usize, 755usize, 1usize),
                        (142usize, 142usize, 756usize, 1usize),
                        (143usize, 143usize, 757usize, 1usize),
                        (144usize, 144usize, 758usize, 1usize),
                        (145usize, 145usize, 759usize, 1usize),
                        (146usize, 146usize, 760usize, 1usize),
                        (147usize, 147usize, 761usize, 1usize),
                        (148usize, 148usize, 762usize, 1usize),
                        (149usize, 149usize, 763usize, 1usize),
                        (150usize, 150usize, 764usize, 1usize),
                        (151usize, 151usize, 765usize, 1usize),
                        (152usize, 152usize, 766usize, 1usize),
                        (153usize, 153usize, 767usize, 1usize),
                        (154usize, 154usize, 768usize, 1usize),
                        (155usize, 155usize, 769usize, 1usize),
                        (156usize, 156usize, 770usize, 1usize),
                        (157usize, 157usize, 771usize, 1usize),
                        (161usize, 0usize, 772usize, 1usize),
                        (161usize, 1usize, 773usize, 1usize),
                        (161usize, 2usize, 774usize, 1usize),
                        (161usize, 5usize, 775usize, 2usize),
                        (161usize, 56usize, 777usize, 2usize),
                        (161usize, 57usize, 779usize, 2usize),
                        (161usize, 58usize, 781usize, 2usize),
                        (161usize, 59usize, 783usize, 2usize),
                        (161usize, 60usize, 785usize, 2usize),
                        (161usize, 61usize, 787usize, 2usize),
                        (161usize, 62usize, 789usize, 2usize),
                        (161usize, 63usize, 791usize, 2usize),
                        (161usize, 64usize, 793usize, 2usize),
                        (161usize, 65usize, 795usize, 2usize),
                        (161usize, 66usize, 797usize, 2usize),
                        (161usize, 67usize, 799usize, 2usize),
                        (161usize, 68usize, 801usize, 2usize),
                        (161usize, 69usize, 803usize, 2usize),
                        (161usize, 70usize, 805usize, 2usize),
                        (161usize, 71usize, 807usize, 2usize),
                        (161usize, 193usize, 809usize, 1usize),
                        (161usize, 194usize, 810usize, 1usize),
                        (161usize, 195usize, 811usize, 1usize),
                        (161usize, 196usize, 812usize, 1usize),
                        (161usize, 197usize, 813usize, 1usize),
                        (161usize, 198usize, 814usize, 1usize),
                        (161usize, 199usize, 815usize, 1usize),
                        (161usize, 200usize, 816usize, 1usize),
                        (161usize, 201usize, 817usize, 1usize),
                        (161usize, 202usize, 818usize, 1usize),
                        (161usize, 203usize, 819usize, 1usize),
                        (161usize, 204usize, 820usize, 1usize),
                        (161usize, 205usize, 821usize, 1usize),
                        (161usize, 206usize, 822usize, 1usize),
                        (161usize, 207usize, 823usize, 1usize),
                        (161usize, 208usize, 824usize, 1usize),
                        (162usize, 0usize, 825usize, 1usize),
                        (162usize, 1usize, 826usize, 1usize),
                        (162usize, 2usize, 827usize, 1usize),
                        (162usize, 5usize, 828usize, 2usize),
                        (162usize, 56usize, 830usize, 2usize),
                        (162usize, 57usize, 832usize, 2usize),
                        (162usize, 58usize, 834usize, 2usize),
                        (162usize, 59usize, 836usize, 2usize),
                        (162usize, 60usize, 838usize, 2usize),
                        (162usize, 61usize, 840usize, 2usize),
                        (162usize, 62usize, 842usize, 2usize),
                        (162usize, 63usize, 844usize, 2usize),
                        (162usize, 64usize, 846usize, 2usize),
                        (162usize, 65usize, 848usize, 2usize),
                        (162usize, 66usize, 850usize, 2usize),
                        (162usize, 67usize, 852usize, 2usize),
                        (162usize, 68usize, 854usize, 2usize),
                        (162usize, 69usize, 856usize, 2usize),
                        (162usize, 70usize, 858usize, 2usize),
                        (162usize, 71usize, 860usize, 2usize),
                        (162usize, 193usize, 862usize, 1usize),
                        (162usize, 194usize, 863usize, 1usize),
                        (162usize, 195usize, 864usize, 1usize),
                        (162usize, 196usize, 865usize, 1usize),
                        (162usize, 197usize, 866usize, 1usize),
                        (162usize, 198usize, 867usize, 1usize),
                        (162usize, 199usize, 868usize, 1usize),
                        (162usize, 200usize, 869usize, 1usize),
                        (162usize, 201usize, 870usize, 1usize),
                        (162usize, 202usize, 871usize, 1usize),
                        (162usize, 203usize, 872usize, 1usize),
                        (162usize, 204usize, 873usize, 1usize),
                        (162usize, 205usize, 874usize, 1usize),
                        (162usize, 206usize, 875usize, 1usize),
                        (162usize, 207usize, 876usize, 1usize),
                        (162usize, 208usize, 877usize, 1usize),
                        (165usize, 0usize, 878usize, 1usize),
                        (165usize, 1usize, 879usize, 1usize),
                        (165usize, 2usize, 880usize, 1usize),
                        (165usize, 5usize, 881usize, 2usize),
                        (165usize, 56usize, 883usize, 2usize),
                        (165usize, 57usize, 885usize, 2usize),
                        (165usize, 58usize, 887usize, 2usize),
                        (165usize, 59usize, 889usize, 2usize),
                        (165usize, 60usize, 891usize, 2usize),
                        (165usize, 61usize, 893usize, 2usize),
                        (165usize, 62usize, 895usize, 2usize),
                        (165usize, 63usize, 897usize, 2usize),
                        (165usize, 64usize, 899usize, 2usize),
                        (165usize, 65usize, 901usize, 2usize),
                        (165usize, 66usize, 903usize, 2usize),
                        (165usize, 67usize, 905usize, 2usize),
                        (165usize, 68usize, 907usize, 2usize),
                        (165usize, 69usize, 909usize, 2usize),
                        (165usize, 70usize, 911usize, 2usize),
                        (165usize, 71usize, 913usize, 2usize),
                        (165usize, 193usize, 915usize, 1usize),
                        (165usize, 194usize, 916usize, 1usize),
                        (165usize, 195usize, 917usize, 1usize),
                        (165usize, 196usize, 918usize, 1usize),
                        (165usize, 197usize, 919usize, 1usize),
                        (165usize, 198usize, 920usize, 1usize),
                        (165usize, 199usize, 921usize, 1usize),
                        (165usize, 200usize, 922usize, 1usize),
                        (165usize, 201usize, 923usize, 1usize),
                        (165usize, 202usize, 924usize, 1usize),
                        (165usize, 203usize, 925usize, 1usize),
                        (165usize, 204usize, 926usize, 1usize),
                        (165usize, 205usize, 927usize, 1usize),
                        (165usize, 206usize, 928usize, 1usize),
                        (165usize, 207usize, 929usize, 1usize),
                        (165usize, 208usize, 930usize, 1usize),
                        (166usize, 0usize, 931usize, 1usize),
                        (166usize, 1usize, 932usize, 1usize),
                        (166usize, 2usize, 933usize, 1usize),
                        (166usize, 5usize, 934usize, 2usize),
                        (166usize, 56usize, 936usize, 2usize),
                        (166usize, 57usize, 938usize, 2usize),
                        (166usize, 58usize, 940usize, 2usize),
                        (166usize, 59usize, 942usize, 2usize),
                        (166usize, 60usize, 944usize, 2usize),
                        (166usize, 61usize, 946usize, 2usize),
                        (166usize, 62usize, 948usize, 2usize),
                        (166usize, 63usize, 950usize, 2usize),
                        (166usize, 64usize, 952usize, 2usize),
                        (166usize, 65usize, 954usize, 2usize),
                        (166usize, 66usize, 956usize, 2usize),
                        (166usize, 67usize, 958usize, 2usize),
                        (166usize, 68usize, 960usize, 2usize),
                        (166usize, 69usize, 962usize, 2usize),
                        (166usize, 70usize, 964usize, 2usize),
                        (166usize, 71usize, 966usize, 2usize),
                        (166usize, 193usize, 968usize, 1usize),
                        (166usize, 194usize, 969usize, 1usize),
                        (166usize, 195usize, 970usize, 1usize),
                        (166usize, 196usize, 971usize, 1usize),
                        (166usize, 197usize, 972usize, 1usize),
                        (166usize, 198usize, 973usize, 1usize),
                        (166usize, 199usize, 974usize, 1usize),
                        (166usize, 200usize, 975usize, 1usize),
                        (166usize, 201usize, 976usize, 1usize),
                        (166usize, 202usize, 977usize, 1usize),
                        (166usize, 203usize, 978usize, 1usize),
                        (166usize, 204usize, 979usize, 1usize),
                        (166usize, 205usize, 980usize, 1usize),
                        (166usize, 206usize, 981usize, 1usize),
                        (166usize, 207usize, 982usize, 1usize),
                        (166usize, 208usize, 983usize, 1usize),
                        (169usize, 0usize, 984usize, 1usize),
                        (169usize, 1usize, 985usize, 1usize),
                        (169usize, 2usize, 986usize, 1usize),
                        (169usize, 5usize, 987usize, 2usize),
                        (169usize, 56usize, 989usize, 2usize),
                        (169usize, 57usize, 991usize, 2usize),
                        (169usize, 58usize, 993usize, 2usize),
                        (169usize, 59usize, 995usize, 2usize),
                        (169usize, 60usize, 997usize, 2usize),
                        (169usize, 61usize, 999usize, 2usize),
                        (169usize, 62usize, 1001usize, 2usize),
                        (169usize, 63usize, 1003usize, 2usize),
                        (169usize, 64usize, 1005usize, 2usize),
                        (169usize, 65usize, 1007usize, 2usize),
                        (169usize, 66usize, 1009usize, 2usize),
                        (169usize, 67usize, 1011usize, 2usize),
                        (169usize, 68usize, 1013usize, 2usize),
                        (169usize, 69usize, 1015usize, 2usize),
                        (169usize, 70usize, 1017usize, 2usize),
                        (169usize, 71usize, 1019usize, 2usize),
                        (169usize, 193usize, 1021usize, 1usize),
                        (169usize, 194usize, 1022usize, 1usize),
                        (169usize, 195usize, 1023usize, 1usize),
                        (169usize, 196usize, 1024usize, 1usize),
                        (169usize, 197usize, 1025usize, 1usize),
                        (169usize, 198usize, 1026usize, 1usize),
                        (169usize, 199usize, 1027usize, 1usize),
                        (169usize, 200usize, 1028usize, 1usize),
                        (169usize, 201usize, 1029usize, 1usize),
                        (169usize, 202usize, 1030usize, 1usize),
                        (169usize, 203usize, 1031usize, 1usize),
                        (169usize, 204usize, 1032usize, 1usize),
                        (169usize, 205usize, 1033usize, 1usize),
                        (169usize, 206usize, 1034usize, 1usize),
                        (169usize, 207usize, 1035usize, 1usize),
                        (169usize, 208usize, 1036usize, 1usize),
                        (170usize, 0usize, 1037usize, 1usize),
                        (170usize, 1usize, 1038usize, 1usize),
                        (170usize, 2usize, 1039usize, 1usize),
                        (170usize, 5usize, 1040usize, 2usize),
                        (170usize, 56usize, 1042usize, 2usize),
                        (170usize, 57usize, 1044usize, 2usize),
                        (170usize, 58usize, 1046usize, 2usize),
                        (170usize, 59usize, 1048usize, 2usize),
                        (170usize, 60usize, 1050usize, 2usize),
                        (170usize, 61usize, 1052usize, 2usize),
                        (170usize, 62usize, 1054usize, 2usize),
                        (170usize, 63usize, 1056usize, 2usize),
                        (170usize, 64usize, 1058usize, 2usize),
                        (170usize, 65usize, 1060usize, 2usize),
                        (170usize, 66usize, 1062usize, 2usize),
                        (170usize, 67usize, 1064usize, 2usize),
                        (170usize, 68usize, 1066usize, 2usize),
                        (170usize, 69usize, 1068usize, 2usize),
                        (170usize, 70usize, 1070usize, 2usize),
                        (170usize, 71usize, 1072usize, 2usize),
                        (170usize, 193usize, 1074usize, 1usize),
                        (170usize, 194usize, 1075usize, 1usize),
                        (170usize, 195usize, 1076usize, 1usize),
                        (170usize, 196usize, 1077usize, 1usize),
                        (170usize, 197usize, 1078usize, 1usize),
                        (170usize, 198usize, 1079usize, 1usize),
                        (170usize, 199usize, 1080usize, 1usize),
                        (170usize, 200usize, 1081usize, 1usize),
                        (170usize, 201usize, 1082usize, 1usize),
                        (170usize, 202usize, 1083usize, 1usize),
                        (170usize, 203usize, 1084usize, 1usize),
                        (170usize, 204usize, 1085usize, 1usize),
                        (170usize, 205usize, 1086usize, 1usize),
                        (170usize, 206usize, 1087usize, 1usize),
                        (170usize, 207usize, 1088usize, 1usize),
                        (170usize, 208usize, 1089usize, 1usize),
                        (173usize, 0usize, 1090usize, 1usize),
                        (173usize, 1usize, 1091usize, 1usize),
                        (173usize, 2usize, 1092usize, 1usize),
                        (173usize, 5usize, 1093usize, 2usize),
                        (173usize, 56usize, 1095usize, 2usize),
                        (173usize, 57usize, 1097usize, 2usize),
                        (173usize, 58usize, 1099usize, 2usize),
                        (173usize, 59usize, 1101usize, 2usize),
                        (173usize, 60usize, 1103usize, 2usize),
                        (173usize, 61usize, 1105usize, 2usize),
                        (173usize, 62usize, 1107usize, 2usize),
                        (173usize, 63usize, 1109usize, 2usize),
                        (173usize, 64usize, 1111usize, 2usize),
                        (173usize, 65usize, 1113usize, 2usize),
                        (173usize, 66usize, 1115usize, 2usize),
                        (173usize, 67usize, 1117usize, 2usize),
                        (173usize, 68usize, 1119usize, 2usize),
                        (173usize, 69usize, 1121usize, 2usize),
                        (173usize, 70usize, 1123usize, 2usize),
                        (173usize, 71usize, 1125usize, 2usize),
                        (173usize, 193usize, 1127usize, 1usize),
                        (173usize, 194usize, 1128usize, 1usize),
                        (173usize, 195usize, 1129usize, 1usize),
                        (173usize, 196usize, 1130usize, 1usize),
                        (173usize, 197usize, 1131usize, 1usize),
                        (173usize, 198usize, 1132usize, 1usize),
                        (173usize, 199usize, 1133usize, 1usize),
                        (173usize, 200usize, 1134usize, 1usize),
                        (173usize, 201usize, 1135usize, 1usize),
                        (173usize, 202usize, 1136usize, 1usize),
                        (173usize, 203usize, 1137usize, 1usize),
                        (173usize, 204usize, 1138usize, 1usize),
                        (173usize, 205usize, 1139usize, 1usize),
                        (173usize, 206usize, 1140usize, 1usize),
                        (173usize, 207usize, 1141usize, 1usize),
                        (173usize, 208usize, 1142usize, 1usize),
                        (174usize, 0usize, 1143usize, 1usize),
                        (174usize, 1usize, 1144usize, 1usize),
                        (174usize, 2usize, 1145usize, 1usize),
                        (174usize, 5usize, 1146usize, 2usize),
                        (174usize, 56usize, 1148usize, 2usize),
                        (174usize, 57usize, 1150usize, 2usize),
                        (174usize, 58usize, 1152usize, 2usize),
                        (174usize, 59usize, 1154usize, 2usize),
                        (174usize, 60usize, 1156usize, 2usize),
                        (174usize, 61usize, 1158usize, 2usize),
                        (174usize, 62usize, 1160usize, 2usize),
                        (174usize, 63usize, 1162usize, 2usize),
                        (174usize, 64usize, 1164usize, 2usize),
                        (174usize, 65usize, 1166usize, 2usize),
                        (174usize, 66usize, 1168usize, 2usize),
                        (174usize, 67usize, 1170usize, 2usize),
                        (174usize, 68usize, 1172usize, 2usize),
                        (174usize, 69usize, 1174usize, 2usize),
                        (174usize, 70usize, 1176usize, 2usize),
                        (174usize, 71usize, 1178usize, 2usize),
                        (174usize, 193usize, 1180usize, 1usize),
                        (174usize, 194usize, 1181usize, 1usize),
                        (174usize, 195usize, 1182usize, 1usize),
                        (174usize, 196usize, 1183usize, 1usize),
                        (174usize, 197usize, 1184usize, 1usize),
                        (174usize, 198usize, 1185usize, 1usize),
                        (174usize, 199usize, 1186usize, 1usize),
                        (174usize, 200usize, 1187usize, 1usize),
                        (174usize, 201usize, 1188usize, 1usize),
                        (174usize, 202usize, 1189usize, 1usize),
                        (174usize, 203usize, 1190usize, 1usize),
                        (174usize, 204usize, 1191usize, 1usize),
                        (174usize, 205usize, 1192usize, 1usize),
                        (174usize, 206usize, 1193usize, 1usize),
                        (174usize, 207usize, 1194usize, 1usize),
                        (174usize, 208usize, 1195usize, 1usize),
                        (177usize, 0usize, 1196usize, 1usize),
                        (177usize, 1usize, 1197usize, 1usize),
                        (177usize, 2usize, 1198usize, 1usize),
                        (177usize, 5usize, 1199usize, 2usize),
                        (177usize, 56usize, 1201usize, 2usize),
                        (177usize, 57usize, 1203usize, 2usize),
                        (177usize, 58usize, 1205usize, 2usize),
                        (177usize, 59usize, 1207usize, 2usize),
                        (177usize, 60usize, 1209usize, 2usize),
                        (177usize, 61usize, 1211usize, 2usize),
                        (177usize, 62usize, 1213usize, 2usize),
                        (177usize, 63usize, 1215usize, 2usize),
                        (177usize, 64usize, 1217usize, 2usize),
                        (177usize, 65usize, 1219usize, 2usize),
                        (177usize, 66usize, 1221usize, 2usize),
                        (177usize, 67usize, 1223usize, 2usize),
                        (177usize, 68usize, 1225usize, 2usize),
                        (177usize, 69usize, 1227usize, 2usize),
                        (177usize, 70usize, 1229usize, 2usize),
                        (177usize, 71usize, 1231usize, 2usize),
                        (177usize, 193usize, 1233usize, 1usize),
                        (177usize, 194usize, 1234usize, 1usize),
                        (177usize, 195usize, 1235usize, 1usize),
                        (177usize, 196usize, 1236usize, 1usize),
                        (177usize, 197usize, 1237usize, 1usize),
                        (177usize, 198usize, 1238usize, 1usize),
                        (177usize, 199usize, 1239usize, 1usize),
                        (177usize, 200usize, 1240usize, 1usize),
                        (177usize, 201usize, 1241usize, 1usize),
                        (177usize, 202usize, 1242usize, 1usize),
                        (177usize, 203usize, 1243usize, 1usize),
                        (177usize, 204usize, 1244usize, 1usize),
                        (177usize, 205usize, 1245usize, 1usize),
                        (177usize, 206usize, 1246usize, 1usize),
                        (177usize, 207usize, 1247usize, 1usize),
                        (177usize, 208usize, 1248usize, 1usize),
                        (178usize, 0usize, 1249usize, 1usize),
                        (178usize, 1usize, 1250usize, 1usize),
                        (178usize, 2usize, 1251usize, 1usize),
                        (178usize, 5usize, 1252usize, 2usize),
                        (178usize, 56usize, 1254usize, 2usize),
                        (178usize, 57usize, 1256usize, 2usize),
                        (178usize, 58usize, 1258usize, 2usize),
                        (178usize, 59usize, 1260usize, 2usize),
                        (178usize, 60usize, 1262usize, 2usize),
                        (178usize, 61usize, 1264usize, 2usize),
                        (178usize, 62usize, 1266usize, 2usize),
                        (178usize, 63usize, 1268usize, 2usize),
                        (178usize, 64usize, 1270usize, 2usize),
                        (178usize, 65usize, 1272usize, 2usize),
                        (178usize, 66usize, 1274usize, 2usize),
                        (178usize, 67usize, 1276usize, 2usize),
                        (178usize, 68usize, 1278usize, 2usize),
                        (178usize, 69usize, 1280usize, 2usize),
                        (178usize, 70usize, 1282usize, 2usize),
                        (178usize, 71usize, 1284usize, 2usize),
                        (178usize, 193usize, 1286usize, 1usize),
                        (178usize, 194usize, 1287usize, 1usize),
                        (178usize, 195usize, 1288usize, 1usize),
                        (178usize, 196usize, 1289usize, 1usize),
                        (178usize, 197usize, 1290usize, 1usize),
                        (178usize, 198usize, 1291usize, 1usize),
                        (178usize, 199usize, 1292usize, 1usize),
                        (178usize, 200usize, 1293usize, 1usize),
                        (178usize, 201usize, 1294usize, 1usize),
                        (178usize, 202usize, 1295usize, 1usize),
                        (178usize, 203usize, 1296usize, 1usize),
                        (178usize, 204usize, 1297usize, 1usize),
                        (178usize, 205usize, 1298usize, 1usize),
                        (178usize, 206usize, 1299usize, 1usize),
                        (178usize, 207usize, 1300usize, 1usize),
                        (178usize, 208usize, 1301usize, 1usize),
                        (181usize, 0usize, 1302usize, 1usize),
                        (181usize, 1usize, 1303usize, 1usize),
                        (181usize, 2usize, 1304usize, 1usize),
                        (181usize, 5usize, 1305usize, 2usize),
                        (181usize, 56usize, 1307usize, 2usize),
                        (181usize, 57usize, 1309usize, 2usize),
                        (181usize, 58usize, 1311usize, 2usize),
                        (181usize, 59usize, 1313usize, 2usize),
                        (181usize, 60usize, 1315usize, 2usize),
                        (181usize, 61usize, 1317usize, 2usize),
                        (181usize, 62usize, 1319usize, 2usize),
                        (181usize, 63usize, 1321usize, 2usize),
                        (181usize, 64usize, 1323usize, 2usize),
                        (181usize, 65usize, 1325usize, 2usize),
                        (181usize, 66usize, 1327usize, 2usize),
                        (181usize, 67usize, 1329usize, 2usize),
                        (181usize, 68usize, 1331usize, 2usize),
                        (181usize, 69usize, 1333usize, 2usize),
                        (181usize, 70usize, 1335usize, 2usize),
                        (181usize, 71usize, 1337usize, 2usize),
                        (181usize, 193usize, 1339usize, 1usize),
                        (181usize, 194usize, 1340usize, 1usize),
                        (181usize, 195usize, 1341usize, 1usize),
                        (181usize, 196usize, 1342usize, 1usize),
                        (181usize, 197usize, 1343usize, 1usize),
                        (181usize, 198usize, 1344usize, 1usize),
                        (181usize, 199usize, 1345usize, 1usize),
                        (181usize, 200usize, 1346usize, 1usize),
                        (181usize, 201usize, 1347usize, 1usize),
                        (181usize, 202usize, 1348usize, 1usize),
                        (181usize, 203usize, 1349usize, 1usize),
                        (181usize, 204usize, 1350usize, 1usize),
                        (181usize, 205usize, 1351usize, 1usize),
                        (181usize, 206usize, 1352usize, 1usize),
                        (181usize, 207usize, 1353usize, 1usize),
                        (181usize, 208usize, 1354usize, 1usize),
                        (182usize, 0usize, 1355usize, 1usize),
                        (182usize, 1usize, 1356usize, 1usize),
                        (182usize, 2usize, 1357usize, 1usize),
                        (182usize, 5usize, 1358usize, 2usize),
                        (182usize, 56usize, 1360usize, 2usize),
                        (182usize, 57usize, 1362usize, 2usize),
                        (182usize, 58usize, 1364usize, 2usize),
                        (182usize, 59usize, 1366usize, 2usize),
                        (182usize, 60usize, 1368usize, 2usize),
                        (182usize, 61usize, 1370usize, 2usize),
                        (182usize, 62usize, 1372usize, 2usize),
                        (182usize, 63usize, 1374usize, 2usize),
                        (182usize, 64usize, 1376usize, 2usize),
                        (182usize, 65usize, 1378usize, 2usize),
                        (182usize, 66usize, 1380usize, 2usize),
                        (182usize, 67usize, 1382usize, 2usize),
                        (182usize, 68usize, 1384usize, 2usize),
                        (182usize, 69usize, 1386usize, 2usize),
                        (182usize, 70usize, 1388usize, 2usize),
                        (182usize, 71usize, 1390usize, 2usize),
                        (182usize, 193usize, 1392usize, 1usize),
                        (182usize, 194usize, 1393usize, 1usize),
                        (182usize, 195usize, 1394usize, 1usize),
                        (182usize, 196usize, 1395usize, 1usize),
                        (182usize, 197usize, 1396usize, 1usize),
                        (182usize, 198usize, 1397usize, 1usize),
                        (182usize, 199usize, 1398usize, 1usize),
                        (182usize, 200usize, 1399usize, 1usize),
                        (182usize, 201usize, 1400usize, 1usize),
                        (182usize, 202usize, 1401usize, 1usize),
                        (182usize, 203usize, 1402usize, 1usize),
                        (182usize, 204usize, 1403usize, 1usize),
                        (182usize, 205usize, 1404usize, 1usize),
                        (182usize, 206usize, 1405usize, 1usize),
                        (182usize, 207usize, 1406usize, 1usize),
                        (182usize, 208usize, 1407usize, 1usize),
                        (185usize, 0usize, 1408usize, 1usize),
                        (185usize, 1usize, 1409usize, 1usize),
                        (185usize, 2usize, 1410usize, 1usize),
                        (185usize, 5usize, 1411usize, 2usize),
                        (185usize, 56usize, 1413usize, 2usize),
                        (185usize, 57usize, 1415usize, 2usize),
                        (185usize, 58usize, 1417usize, 2usize),
                        (185usize, 59usize, 1419usize, 2usize),
                        (185usize, 60usize, 1421usize, 2usize),
                        (185usize, 61usize, 1423usize, 2usize),
                        (185usize, 62usize, 1425usize, 2usize),
                        (185usize, 63usize, 1427usize, 2usize),
                        (185usize, 64usize, 1429usize, 2usize),
                        (185usize, 65usize, 1431usize, 2usize),
                        (185usize, 66usize, 1433usize, 2usize),
                        (185usize, 67usize, 1435usize, 2usize),
                        (185usize, 68usize, 1437usize, 2usize),
                        (185usize, 69usize, 1439usize, 2usize),
                        (185usize, 70usize, 1441usize, 2usize),
                        (185usize, 71usize, 1443usize, 2usize),
                        (185usize, 193usize, 1445usize, 1usize),
                        (185usize, 194usize, 1446usize, 1usize),
                        (185usize, 195usize, 1447usize, 1usize),
                        (185usize, 196usize, 1448usize, 1usize),
                        (185usize, 197usize, 1449usize, 1usize),
                        (185usize, 198usize, 1450usize, 1usize),
                        (185usize, 199usize, 1451usize, 1usize),
                        (185usize, 200usize, 1452usize, 1usize),
                        (185usize, 201usize, 1453usize, 1usize),
                        (185usize, 202usize, 1454usize, 1usize),
                        (185usize, 203usize, 1455usize, 1usize),
                        (185usize, 204usize, 1456usize, 1usize),
                        (185usize, 205usize, 1457usize, 1usize),
                        (185usize, 206usize, 1458usize, 1usize),
                        (185usize, 207usize, 1459usize, 1usize),
                        (185usize, 208usize, 1460usize, 1usize),
                        (186usize, 0usize, 1461usize, 1usize),
                        (186usize, 1usize, 1462usize, 1usize),
                        (186usize, 2usize, 1463usize, 1usize),
                        (186usize, 5usize, 1464usize, 2usize),
                        (186usize, 56usize, 1466usize, 2usize),
                        (186usize, 57usize, 1468usize, 2usize),
                        (186usize, 58usize, 1470usize, 2usize),
                        (186usize, 59usize, 1472usize, 2usize),
                        (186usize, 60usize, 1474usize, 2usize),
                        (186usize, 61usize, 1476usize, 2usize),
                        (186usize, 62usize, 1478usize, 2usize),
                        (186usize, 63usize, 1480usize, 2usize),
                        (186usize, 64usize, 1482usize, 2usize),
                        (186usize, 65usize, 1484usize, 2usize),
                        (186usize, 66usize, 1486usize, 2usize),
                        (186usize, 67usize, 1488usize, 2usize),
                        (186usize, 68usize, 1490usize, 2usize),
                        (186usize, 69usize, 1492usize, 2usize),
                        (186usize, 70usize, 1494usize, 2usize),
                        (186usize, 71usize, 1496usize, 2usize),
                        (186usize, 193usize, 1498usize, 1usize),
                        (186usize, 194usize, 1499usize, 1usize),
                        (186usize, 195usize, 1500usize, 1usize),
                        (186usize, 196usize, 1501usize, 1usize),
                        (186usize, 197usize, 1502usize, 1usize),
                        (186usize, 198usize, 1503usize, 1usize),
                        (186usize, 199usize, 1504usize, 1usize),
                        (186usize, 200usize, 1505usize, 1usize),
                        (186usize, 201usize, 1506usize, 1usize),
                        (186usize, 202usize, 1507usize, 1usize),
                        (186usize, 203usize, 1508usize, 1usize),
                        (186usize, 204usize, 1509usize, 1usize),
                        (186usize, 205usize, 1510usize, 1usize),
                        (186usize, 206usize, 1511usize, 1usize),
                        (186usize, 207usize, 1512usize, 1usize),
                        (186usize, 208usize, 1513usize, 1usize),
                        (189usize, 0usize, 1514usize, 1usize),
                        (189usize, 1usize, 1515usize, 1usize),
                        (189usize, 2usize, 1516usize, 1usize),
                        (189usize, 5usize, 1517usize, 2usize),
                        (189usize, 56usize, 1519usize, 2usize),
                        (189usize, 57usize, 1521usize, 2usize),
                        (189usize, 58usize, 1523usize, 2usize),
                        (189usize, 59usize, 1525usize, 2usize),
                        (189usize, 60usize, 1527usize, 2usize),
                        (189usize, 61usize, 1529usize, 2usize),
                        (189usize, 62usize, 1531usize, 2usize),
                        (189usize, 63usize, 1533usize, 2usize),
                        (189usize, 64usize, 1535usize, 2usize),
                        (189usize, 65usize, 1537usize, 2usize),
                        (189usize, 66usize, 1539usize, 2usize),
                        (189usize, 67usize, 1541usize, 2usize),
                        (189usize, 68usize, 1543usize, 2usize),
                        (189usize, 69usize, 1545usize, 2usize),
                        (189usize, 70usize, 1547usize, 2usize),
                        (189usize, 71usize, 1549usize, 2usize),
                        (189usize, 193usize, 1551usize, 1usize),
                        (189usize, 194usize, 1552usize, 1usize),
                        (189usize, 195usize, 1553usize, 1usize),
                        (189usize, 196usize, 1554usize, 1usize),
                        (189usize, 197usize, 1555usize, 1usize),
                        (189usize, 198usize, 1556usize, 1usize),
                        (189usize, 199usize, 1557usize, 1usize),
                        (189usize, 200usize, 1558usize, 1usize),
                        (189usize, 201usize, 1559usize, 1usize),
                        (189usize, 202usize, 1560usize, 1usize),
                        (189usize, 203usize, 1561usize, 1usize),
                        (189usize, 204usize, 1562usize, 1usize),
                        (189usize, 205usize, 1563usize, 1usize),
                        (189usize, 206usize, 1564usize, 1usize),
                        (189usize, 207usize, 1565usize, 1usize),
                        (189usize, 208usize, 1566usize, 1usize),
                        (190usize, 0usize, 1567usize, 1usize),
                        (190usize, 1usize, 1568usize, 1usize),
                        (190usize, 2usize, 1569usize, 1usize),
                        (190usize, 5usize, 1570usize, 2usize),
                        (190usize, 56usize, 1572usize, 2usize),
                        (190usize, 57usize, 1574usize, 2usize),
                        (190usize, 58usize, 1576usize, 2usize),
                        (190usize, 59usize, 1578usize, 2usize),
                        (190usize, 60usize, 1580usize, 2usize),
                        (190usize, 61usize, 1582usize, 2usize),
                        (190usize, 62usize, 1584usize, 2usize),
                        (190usize, 63usize, 1586usize, 2usize),
                        (190usize, 64usize, 1588usize, 2usize),
                        (190usize, 65usize, 1590usize, 2usize),
                        (190usize, 66usize, 1592usize, 2usize),
                        (190usize, 67usize, 1594usize, 2usize),
                        (190usize, 68usize, 1596usize, 2usize),
                        (190usize, 69usize, 1598usize, 2usize),
                        (190usize, 70usize, 1600usize, 2usize),
                        (190usize, 71usize, 1602usize, 2usize),
                        (190usize, 193usize, 1604usize, 1usize),
                        (190usize, 194usize, 1605usize, 1usize),
                        (190usize, 195usize, 1606usize, 1usize),
                        (190usize, 196usize, 1607usize, 1usize),
                        (190usize, 197usize, 1608usize, 1usize),
                        (190usize, 198usize, 1609usize, 1usize),
                        (190usize, 199usize, 1610usize, 1usize),
                        (190usize, 200usize, 1611usize, 1usize),
                        (190usize, 201usize, 1612usize, 1usize),
                        (190usize, 202usize, 1613usize, 1usize),
                        (190usize, 203usize, 1614usize, 1usize),
                        (190usize, 204usize, 1615usize, 1usize),
                        (190usize, 205usize, 1616usize, 1usize),
                        (190usize, 206usize, 1617usize, 1usize),
                        (190usize, 207usize, 1618usize, 1usize),
                        (190usize, 208usize, 1619usize, 1usize),
                        (193usize, 0usize, 1620usize, 1usize),
                        (193usize, 1usize, 1621usize, 1usize),
                        (193usize, 2usize, 1622usize, 1usize),
                        (193usize, 5usize, 1623usize, 1usize),
                        (193usize, 7usize, 1624usize, 1usize),
                        (193usize, 40usize, 1625usize, 2usize),
                        (193usize, 41usize, 1627usize, 2usize),
                        (193usize, 42usize, 1629usize, 2usize),
                        (193usize, 43usize, 1631usize, 2usize),
                        (193usize, 44usize, 1633usize, 2usize),
                        (193usize, 45usize, 1635usize, 2usize),
                        (193usize, 46usize, 1637usize, 2usize),
                        (193usize, 47usize, 1639usize, 2usize),
                        (193usize, 48usize, 1641usize, 2usize),
                        (193usize, 49usize, 1643usize, 2usize),
                        (193usize, 50usize, 1645usize, 2usize),
                        (193usize, 51usize, 1647usize, 2usize),
                        (193usize, 52usize, 1649usize, 2usize),
                        (193usize, 53usize, 1651usize, 2usize),
                        (193usize, 54usize, 1653usize, 2usize),
                        (193usize, 55usize, 1655usize, 2usize),
                        (194usize, 0usize, 1657usize, 1usize),
                        (194usize, 1usize, 1658usize, 1usize),
                        (194usize, 2usize, 1659usize, 1usize),
                        (194usize, 5usize, 1660usize, 1usize),
                        (194usize, 7usize, 1661usize, 1usize),
                        (194usize, 40usize, 1662usize, 2usize),
                        (194usize, 41usize, 1664usize, 2usize),
                        (194usize, 42usize, 1666usize, 2usize),
                        (194usize, 43usize, 1668usize, 2usize),
                        (194usize, 44usize, 1670usize, 2usize),
                        (194usize, 45usize, 1672usize, 2usize),
                        (194usize, 46usize, 1674usize, 2usize),
                        (194usize, 47usize, 1676usize, 2usize),
                        (194usize, 48usize, 1678usize, 2usize),
                        (194usize, 49usize, 1680usize, 2usize),
                        (194usize, 50usize, 1682usize, 2usize),
                        (194usize, 51usize, 1684usize, 2usize),
                        (194usize, 52usize, 1686usize, 2usize),
                        (194usize, 53usize, 1688usize, 2usize),
                        (194usize, 54usize, 1690usize, 2usize),
                        (194usize, 55usize, 1692usize, 2usize),
                        (195usize, 0usize, 1694usize, 1usize),
                        (195usize, 1usize, 1695usize, 1usize),
                        (195usize, 2usize, 1696usize, 1usize),
                        (195usize, 5usize, 1697usize, 1usize),
                        (195usize, 7usize, 1698usize, 1usize),
                        (195usize, 40usize, 1699usize, 2usize),
                        (195usize, 41usize, 1701usize, 2usize),
                        (195usize, 42usize, 1703usize, 2usize),
                        (195usize, 43usize, 1705usize, 2usize),
                        (195usize, 44usize, 1707usize, 2usize),
                        (195usize, 45usize, 1709usize, 2usize),
                        (195usize, 46usize, 1711usize, 2usize),
                        (195usize, 47usize, 1713usize, 2usize),
                        (195usize, 48usize, 1715usize, 2usize),
                        (195usize, 49usize, 1717usize, 2usize),
                        (195usize, 50usize, 1719usize, 2usize),
                        (195usize, 51usize, 1721usize, 2usize),
                        (195usize, 52usize, 1723usize, 2usize),
                        (195usize, 53usize, 1725usize, 2usize),
                        (195usize, 54usize, 1727usize, 2usize),
                        (195usize, 55usize, 1729usize, 2usize),
                        (196usize, 0usize, 1731usize, 1usize),
                        (196usize, 1usize, 1732usize, 1usize),
                        (196usize, 2usize, 1733usize, 1usize),
                        (196usize, 5usize, 1734usize, 1usize),
                        (196usize, 7usize, 1735usize, 1usize),
                        (196usize, 40usize, 1736usize, 2usize),
                        (196usize, 41usize, 1738usize, 2usize),
                        (196usize, 42usize, 1740usize, 2usize),
                        (196usize, 43usize, 1742usize, 2usize),
                        (196usize, 44usize, 1744usize, 2usize),
                        (196usize, 45usize, 1746usize, 2usize),
                        (196usize, 46usize, 1748usize, 2usize),
                        (196usize, 47usize, 1750usize, 2usize),
                        (196usize, 48usize, 1752usize, 2usize),
                        (196usize, 49usize, 1754usize, 2usize),
                        (196usize, 50usize, 1756usize, 2usize),
                        (196usize, 51usize, 1758usize, 2usize),
                        (196usize, 52usize, 1760usize, 2usize),
                        (196usize, 53usize, 1762usize, 2usize),
                        (196usize, 54usize, 1764usize, 2usize),
                        (196usize, 55usize, 1766usize, 2usize),
                        (197usize, 0usize, 1768usize, 1usize),
                        (197usize, 1usize, 1769usize, 1usize),
                        (197usize, 2usize, 1770usize, 1usize),
                        (197usize, 5usize, 1771usize, 1usize),
                        (197usize, 7usize, 1772usize, 1usize),
                        (197usize, 40usize, 1773usize, 2usize),
                        (197usize, 41usize, 1775usize, 2usize),
                        (197usize, 42usize, 1777usize, 2usize),
                        (197usize, 43usize, 1779usize, 2usize),
                        (197usize, 44usize, 1781usize, 2usize),
                        (197usize, 45usize, 1783usize, 2usize),
                        (197usize, 46usize, 1785usize, 2usize),
                        (197usize, 47usize, 1787usize, 2usize),
                        (197usize, 48usize, 1789usize, 2usize),
                        (197usize, 49usize, 1791usize, 2usize),
                        (197usize, 50usize, 1793usize, 2usize),
                        (197usize, 51usize, 1795usize, 2usize),
                        (197usize, 52usize, 1797usize, 2usize),
                        (197usize, 53usize, 1799usize, 2usize),
                        (197usize, 54usize, 1801usize, 2usize),
                        (197usize, 55usize, 1803usize, 2usize),
                        (198usize, 0usize, 1805usize, 1usize),
                        (198usize, 1usize, 1806usize, 1usize),
                        (198usize, 2usize, 1807usize, 1usize),
                        (198usize, 5usize, 1808usize, 1usize),
                        (198usize, 7usize, 1809usize, 1usize),
                        (198usize, 40usize, 1810usize, 2usize),
                        (198usize, 41usize, 1812usize, 2usize),
                        (198usize, 42usize, 1814usize, 2usize),
                        (198usize, 43usize, 1816usize, 2usize),
                        (198usize, 44usize, 1818usize, 2usize),
                        (198usize, 45usize, 1820usize, 2usize),
                        (198usize, 46usize, 1822usize, 2usize),
                        (198usize, 47usize, 1824usize, 2usize),
                        (198usize, 48usize, 1826usize, 2usize),
                        (198usize, 49usize, 1828usize, 2usize),
                        (198usize, 50usize, 1830usize, 2usize),
                        (198usize, 51usize, 1832usize, 2usize),
                        (198usize, 52usize, 1834usize, 2usize),
                        (198usize, 53usize, 1836usize, 2usize),
                        (198usize, 54usize, 1838usize, 2usize),
                        (198usize, 55usize, 1840usize, 2usize),
                        (199usize, 0usize, 1842usize, 1usize),
                        (199usize, 1usize, 1843usize, 1usize),
                        (199usize, 2usize, 1844usize, 1usize),
                        (199usize, 5usize, 1845usize, 1usize),
                        (199usize, 7usize, 1846usize, 1usize),
                        (199usize, 40usize, 1847usize, 2usize),
                        (199usize, 41usize, 1849usize, 2usize),
                        (199usize, 42usize, 1851usize, 2usize),
                        (199usize, 43usize, 1853usize, 2usize),
                        (199usize, 44usize, 1855usize, 2usize),
                        (199usize, 45usize, 1857usize, 2usize),
                        (199usize, 46usize, 1859usize, 2usize),
                        (199usize, 47usize, 1861usize, 2usize),
                        (199usize, 48usize, 1863usize, 2usize),
                        (199usize, 49usize, 1865usize, 2usize),
                        (199usize, 50usize, 1867usize, 2usize),
                        (199usize, 51usize, 1869usize, 2usize),
                        (199usize, 52usize, 1871usize, 2usize),
                        (199usize, 53usize, 1873usize, 2usize),
                        (199usize, 54usize, 1875usize, 2usize),
                        (199usize, 55usize, 1877usize, 2usize),
                        (200usize, 0usize, 1879usize, 1usize),
                        (200usize, 1usize, 1880usize, 1usize),
                        (200usize, 2usize, 1881usize, 1usize),
                        (200usize, 5usize, 1882usize, 1usize),
                        (200usize, 7usize, 1883usize, 1usize),
                        (200usize, 40usize, 1884usize, 2usize),
                        (200usize, 41usize, 1886usize, 2usize),
                        (200usize, 42usize, 1888usize, 2usize),
                        (200usize, 43usize, 1890usize, 2usize),
                        (200usize, 44usize, 1892usize, 2usize),
                        (200usize, 45usize, 1894usize, 2usize),
                        (200usize, 46usize, 1896usize, 2usize),
                        (200usize, 47usize, 1898usize, 2usize),
                        (200usize, 48usize, 1900usize, 2usize),
                        (200usize, 49usize, 1902usize, 2usize),
                        (200usize, 50usize, 1904usize, 2usize),
                        (200usize, 51usize, 1906usize, 2usize),
                        (200usize, 52usize, 1908usize, 2usize),
                        (200usize, 53usize, 1910usize, 2usize),
                        (200usize, 54usize, 1912usize, 2usize),
                        (200usize, 55usize, 1914usize, 2usize),
                        (201usize, 0usize, 1916usize, 1usize),
                        (201usize, 1usize, 1917usize, 1usize),
                        (201usize, 2usize, 1918usize, 1usize),
                        (201usize, 5usize, 1919usize, 1usize),
                        (201usize, 7usize, 1920usize, 1usize),
                        (201usize, 40usize, 1921usize, 2usize),
                        (201usize, 41usize, 1923usize, 2usize),
                        (201usize, 42usize, 1925usize, 2usize),
                        (201usize, 43usize, 1927usize, 2usize),
                        (201usize, 44usize, 1929usize, 2usize),
                        (201usize, 45usize, 1931usize, 2usize),
                        (201usize, 46usize, 1933usize, 2usize),
                        (201usize, 47usize, 1935usize, 2usize),
                        (201usize, 48usize, 1937usize, 2usize),
                        (201usize, 49usize, 1939usize, 2usize),
                        (201usize, 50usize, 1941usize, 2usize),
                        (201usize, 51usize, 1943usize, 2usize),
                        (201usize, 52usize, 1945usize, 2usize),
                        (201usize, 53usize, 1947usize, 2usize),
                        (201usize, 54usize, 1949usize, 2usize),
                        (201usize, 55usize, 1951usize, 2usize),
                        (202usize, 0usize, 1953usize, 1usize),
                        (202usize, 1usize, 1954usize, 1usize),
                        (202usize, 2usize, 1955usize, 1usize),
                        (202usize, 5usize, 1956usize, 1usize),
                        (202usize, 7usize, 1957usize, 1usize),
                        (202usize, 40usize, 1958usize, 2usize),
                        (202usize, 41usize, 1960usize, 2usize),
                        (202usize, 42usize, 1962usize, 2usize),
                        (202usize, 43usize, 1964usize, 2usize),
                        (202usize, 44usize, 1966usize, 2usize),
                        (202usize, 45usize, 1968usize, 2usize),
                        (202usize, 46usize, 1970usize, 2usize),
                        (202usize, 47usize, 1972usize, 2usize),
                        (202usize, 48usize, 1974usize, 2usize),
                        (202usize, 49usize, 1976usize, 2usize),
                        (202usize, 50usize, 1978usize, 2usize),
                        (202usize, 51usize, 1980usize, 2usize),
                        (202usize, 52usize, 1982usize, 2usize),
                        (202usize, 53usize, 1984usize, 2usize),
                        (202usize, 54usize, 1986usize, 2usize),
                        (202usize, 55usize, 1988usize, 2usize),
                        (203usize, 0usize, 1990usize, 1usize),
                        (203usize, 1usize, 1991usize, 1usize),
                        (203usize, 2usize, 1992usize, 1usize),
                        (203usize, 5usize, 1993usize, 1usize),
                        (203usize, 7usize, 1994usize, 1usize),
                        (203usize, 40usize, 1995usize, 2usize),
                        (203usize, 41usize, 1997usize, 2usize),
                        (203usize, 42usize, 1999usize, 2usize),
                        (203usize, 43usize, 2001usize, 2usize),
                        (203usize, 44usize, 2003usize, 2usize),
                        (203usize, 45usize, 2005usize, 2usize),
                        (203usize, 46usize, 2007usize, 2usize),
                        (203usize, 47usize, 2009usize, 2usize),
                        (203usize, 48usize, 2011usize, 2usize),
                        (203usize, 49usize, 2013usize, 2usize),
                        (203usize, 50usize, 2015usize, 2usize),
                        (203usize, 51usize, 2017usize, 2usize),
                        (203usize, 52usize, 2019usize, 2usize),
                        (203usize, 53usize, 2021usize, 2usize),
                        (203usize, 54usize, 2023usize, 2usize),
                        (203usize, 55usize, 2025usize, 2usize),
                        (204usize, 0usize, 2027usize, 1usize),
                        (204usize, 1usize, 2028usize, 1usize),
                        (204usize, 2usize, 2029usize, 1usize),
                        (204usize, 5usize, 2030usize, 1usize),
                        (204usize, 7usize, 2031usize, 1usize),
                        (204usize, 40usize, 2032usize, 2usize),
                        (204usize, 41usize, 2034usize, 2usize),
                        (204usize, 42usize, 2036usize, 2usize),
                        (204usize, 43usize, 2038usize, 2usize),
                        (204usize, 44usize, 2040usize, 2usize),
                        (204usize, 45usize, 2042usize, 2usize),
                        (204usize, 46usize, 2044usize, 2usize),
                        (204usize, 47usize, 2046usize, 2usize),
                        (204usize, 48usize, 2048usize, 2usize),
                        (204usize, 49usize, 2050usize, 2usize),
                        (204usize, 50usize, 2052usize, 2usize),
                        (204usize, 51usize, 2054usize, 2usize),
                        (204usize, 52usize, 2056usize, 2usize),
                        (204usize, 53usize, 2058usize, 2usize),
                        (204usize, 54usize, 2060usize, 2usize),
                        (204usize, 55usize, 2062usize, 2usize),
                        (205usize, 0usize, 2064usize, 1usize),
                        (205usize, 1usize, 2065usize, 1usize),
                        (205usize, 2usize, 2066usize, 1usize),
                        (205usize, 5usize, 2067usize, 1usize),
                        (205usize, 7usize, 2068usize, 1usize),
                        (205usize, 40usize, 2069usize, 2usize),
                        (205usize, 41usize, 2071usize, 2usize),
                        (205usize, 42usize, 2073usize, 2usize),
                        (205usize, 43usize, 2075usize, 2usize),
                        (205usize, 44usize, 2077usize, 2usize),
                        (205usize, 45usize, 2079usize, 2usize),
                        (205usize, 46usize, 2081usize, 2usize),
                        (205usize, 47usize, 2083usize, 2usize),
                        (205usize, 48usize, 2085usize, 2usize),
                        (205usize, 49usize, 2087usize, 2usize),
                        (205usize, 50usize, 2089usize, 2usize),
                        (205usize, 51usize, 2091usize, 2usize),
                        (205usize, 52usize, 2093usize, 2usize),
                        (205usize, 53usize, 2095usize, 2usize),
                        (205usize, 54usize, 2097usize, 2usize),
                        (205usize, 55usize, 2099usize, 2usize),
                        (206usize, 0usize, 2101usize, 1usize),
                        (206usize, 1usize, 2102usize, 1usize),
                        (206usize, 2usize, 2103usize, 1usize),
                        (206usize, 5usize, 2104usize, 1usize),
                        (206usize, 7usize, 2105usize, 1usize),
                        (206usize, 40usize, 2106usize, 2usize),
                        (206usize, 41usize, 2108usize, 2usize),
                        (206usize, 42usize, 2110usize, 2usize),
                        (206usize, 43usize, 2112usize, 2usize),
                        (206usize, 44usize, 2114usize, 2usize),
                        (206usize, 45usize, 2116usize, 2usize),
                        (206usize, 46usize, 2118usize, 2usize),
                        (206usize, 47usize, 2120usize, 2usize),
                        (206usize, 48usize, 2122usize, 2usize),
                        (206usize, 49usize, 2124usize, 2usize),
                        (206usize, 50usize, 2126usize, 2usize),
                        (206usize, 51usize, 2128usize, 2usize),
                        (206usize, 52usize, 2130usize, 2usize),
                        (206usize, 53usize, 2132usize, 2usize),
                        (206usize, 54usize, 2134usize, 2usize),
                        (206usize, 55usize, 2136usize, 2usize),
                        (207usize, 0usize, 2138usize, 1usize),
                        (207usize, 1usize, 2139usize, 1usize),
                        (207usize, 2usize, 2140usize, 1usize),
                        (207usize, 5usize, 2141usize, 1usize),
                        (207usize, 7usize, 2142usize, 1usize),
                        (207usize, 40usize, 2143usize, 2usize),
                        (207usize, 41usize, 2145usize, 2usize),
                        (207usize, 42usize, 2147usize, 2usize),
                        (207usize, 43usize, 2149usize, 2usize),
                        (207usize, 44usize, 2151usize, 2usize),
                        (207usize, 45usize, 2153usize, 2usize),
                        (207usize, 46usize, 2155usize, 2usize),
                        (207usize, 47usize, 2157usize, 2usize),
                        (207usize, 48usize, 2159usize, 2usize),
                        (207usize, 49usize, 2161usize, 2usize),
                        (207usize, 50usize, 2163usize, 2usize),
                        (207usize, 51usize, 2165usize, 2usize),
                        (207usize, 52usize, 2167usize, 2usize),
                        (207usize, 53usize, 2169usize, 2usize),
                        (207usize, 54usize, 2171usize, 2usize),
                        (207usize, 55usize, 2173usize, 2usize),
                        (208usize, 0usize, 2175usize, 1usize),
                        (208usize, 1usize, 2176usize, 1usize),
                        (208usize, 2usize, 2177usize, 1usize),
                        (208usize, 5usize, 2178usize, 1usize),
                        (208usize, 7usize, 2179usize, 1usize),
                        (208usize, 40usize, 2180usize, 2usize),
                        (208usize, 41usize, 2182usize, 2usize),
                        (208usize, 42usize, 2184usize, 2usize),
                        (208usize, 43usize, 2186usize, 2usize),
                        (208usize, 44usize, 2188usize, 2usize),
                        (208usize, 45usize, 2190usize, 2usize),
                        (208usize, 46usize, 2192usize, 2usize),
                        (208usize, 47usize, 2194usize, 2usize),
                        (208usize, 48usize, 2196usize, 2usize),
                        (208usize, 49usize, 2198usize, 2usize),
                        (208usize, 50usize, 2200usize, 2usize),
                        (208usize, 51usize, 2202usize, 2usize),
                        (208usize, 52usize, 2204usize, 2usize),
                        (208usize, 53usize, 2206usize, 2usize),
                        (208usize, 54usize, 2208usize, 2usize),
                        (208usize, 55usize, 2210usize, 2usize),
                        (212usize, 212usize, 2212usize, 1usize),
                    ];
                    const CK_QUAD_TERMS: [(u32, usize); 2213usize] = [
                        (268435454u32, 2usize),
                        (268435454u32, 71usize),
                        (536870908u32, 2usize),
                        (536870908u32, 2usize),
                        (536870908u32, 2usize),
                        (536870908u32, 2usize),
                        (536870908u32, 2usize),
                        (268435454u32, 3usize),
                        (536870908u32, 2usize),
                        (1744830467u32, 3usize),
                        (268435454u32, 51usize),
                        (1744830467u32, 4usize),
                        (268435454u32, 52usize),
                        (1744830467u32, 5usize),
                        (268435454u32, 53usize),
                        (1744830467u32, 6usize),
                        (268435454u32, 54usize),
                        (1744830467u32, 7usize),
                        (268435454u32, 55usize),
                        (1744830467u32, 8usize),
                        (268435454u32, 56usize),
                        (1744830467u32, 9usize),
                        (268435454u32, 57usize),
                        (1744830467u32, 10usize),
                        (268435454u32, 58usize),
                        (1744830467u32, 11usize),
                        (268435454u32, 59usize),
                        (1744830467u32, 12usize),
                        (268435454u32, 60usize),
                        (1744830467u32, 13usize),
                        (268435454u32, 61usize),
                        (1744830467u32, 14usize),
                        (268435454u32, 62usize),
                        (1744830467u32, 15usize),
                        (268435454u32, 63usize),
                        (1744830467u32, 16usize),
                        (268435454u32, 64usize),
                        (1744830467u32, 17usize),
                        (268435454u32, 65usize),
                        (1744830467u32, 18usize),
                        (268435454u32, 66usize),
                        (268435454u32, 69usize),
                        (268435454u32, 2usize),
                        (268435454u32, 72usize),
                        (536870908u32, 2usize),
                        (536870908u32, 2usize),
                        (536870908u32, 2usize),
                        (536870908u32, 2usize),
                        (268435454u32, 3usize),
                        (536870908u32, 2usize),
                        (268435454u32, 3usize),
                        (268435454u32, 51usize),
                        (268435454u32, 4usize),
                        (268435454u32, 52usize),
                        (268435454u32, 5usize),
                        (268435454u32, 53usize),
                        (268435454u32, 6usize),
                        (268435454u32, 54usize),
                        (268435454u32, 7usize),
                        (268435454u32, 55usize),
                        (268435454u32, 8usize),
                        (268435454u32, 56usize),
                        (268435454u32, 9usize),
                        (268435454u32, 57usize),
                        (268435454u32, 10usize),
                        (268435454u32, 58usize),
                        (268435454u32, 11usize),
                        (268435454u32, 59usize),
                        (268435454u32, 12usize),
                        (268435454u32, 60usize),
                        (268435454u32, 13usize),
                        (268435454u32, 61usize),
                        (268435454u32, 14usize),
                        (268435454u32, 62usize),
                        (268435454u32, 15usize),
                        (268435454u32, 63usize),
                        (268435454u32, 16usize),
                        (268435454u32, 64usize),
                        (268435454u32, 17usize),
                        (268435454u32, 65usize),
                        (268435454u32, 18usize),
                        (268435454u32, 66usize),
                        (268435454u32, 69usize),
                        (268435454u32, 2usize),
                        (268435454u32, 73usize),
                        (536870908u32, 2usize),
                        (536870908u32, 2usize),
                        (536870908u32, 2usize),
                        (268435454u32, 3usize),
                        (536870908u32, 2usize),
                        (268435454u32, 3usize),
                        (268435454u32, 51usize),
                        (268435454u32, 4usize),
                        (268435454u32, 52usize),
                        (268435454u32, 5usize),
                        (268435454u32, 53usize),
                        (268435454u32, 6usize),
                        (268435454u32, 54usize),
                        (268435454u32, 7usize),
                        (268435454u32, 55usize),
                        (268435454u32, 8usize),
                        (268435454u32, 56usize),
                        (268435454u32, 9usize),
                        (268435454u32, 57usize),
                        (268435454u32, 10usize),
                        (268435454u32, 58usize),
                        (268435454u32, 11usize),
                        (268435454u32, 59usize),
                        (268435454u32, 12usize),
                        (268435454u32, 60usize),
                        (268435454u32, 13usize),
                        (268435454u32, 61usize),
                        (268435454u32, 14usize),
                        (268435454u32, 62usize),
                        (268435454u32, 15usize),
                        (268435454u32, 63usize),
                        (268435454u32, 16usize),
                        (268435454u32, 64usize),
                        (268435454u32, 17usize),
                        (268435454u32, 65usize),
                        (268435454u32, 18usize),
                        (268435454u32, 66usize),
                        (268435454u32, 69usize),
                        (268435454u32, 2usize),
                        (268435454u32, 74usize),
                        (536870908u32, 2usize),
                        (536870908u32, 2usize),
                        (536870908u32, 2usize),
                        (268435454u32, 51usize),
                        (268435454u32, 52usize),
                        (268435454u32, 53usize),
                        (268435454u32, 54usize),
                        (268435454u32, 55usize),
                        (268435454u32, 56usize),
                        (268435454u32, 57usize),
                        (268435454u32, 58usize),
                        (268435454u32, 59usize),
                        (268435454u32, 60usize),
                        (268435454u32, 61usize),
                        (268435454u32, 62usize),
                        (268435454u32, 63usize),
                        (268435454u32, 64usize),
                        (268435454u32, 65usize),
                        (268435454u32, 66usize),
                        (1744830467u32, 69usize),
                        (268435454u32, 2usize),
                        (268435454u32, 75usize),
                        (536870908u32, 2usize),
                        (536870908u32, 2usize),
                        (268435454u32, 51usize),
                        (268435454u32, 52usize),
                        (268435454u32, 53usize),
                        (268435454u32, 54usize),
                        (268435454u32, 55usize),
                        (268435454u32, 56usize),
                        (268435454u32, 57usize),
                        (268435454u32, 58usize),
                        (268435454u32, 59usize),
                        (268435454u32, 60usize),
                        (268435454u32, 61usize),
                        (268435454u32, 62usize),
                        (268435454u32, 63usize),
                        (268435454u32, 64usize),
                        (268435454u32, 65usize),
                        (268435454u32, 66usize),
                        (268435454u32, 2usize),
                        (268435454u32, 76usize),
                        (536870908u32, 2usize),
                        (268435454u32, 3usize),
                        (268435454u32, 4usize),
                        (268435454u32, 5usize),
                        (268435454u32, 6usize),
                        (268435454u32, 7usize),
                        (268435454u32, 8usize),
                        (268435454u32, 9usize),
                        (268435454u32, 10usize),
                        (268435454u32, 11usize),
                        (268435454u32, 12usize),
                        (268435454u32, 13usize),
                        (268435454u32, 14usize),
                        (268435454u32, 15usize),
                        (268435454u32, 16usize),
                        (268435454u32, 17usize),
                        (268435454u32, 18usize),
                        (268435454u32, 68usize),
                        (268435454u32, 69usize),
                        (268435454u32, 77usize),
                        (268435454u32, 3usize),
                        (268435454u32, 2usize),
                        (268435454u32, 78usize),
                        (1744830467u32, 3usize),
                        (268435454u32, 51usize),
                        (1744830467u32, 4usize),
                        (268435454u32, 52usize),
                        (1744830467u32, 5usize),
                        (268435454u32, 53usize),
                        (1744830467u32, 6usize),
                        (268435454u32, 54usize),
                        (1744830467u32, 7usize),
                        (268435454u32, 55usize),
                        (1744830467u32, 8usize),
                        (268435454u32, 56usize),
                        (1744830467u32, 9usize),
                        (268435454u32, 57usize),
                        (1744830467u32, 10usize),
                        (268435454u32, 58usize),
                        (1744830467u32, 11usize),
                        (268435454u32, 59usize),
                        (1744830467u32, 12usize),
                        (268435454u32, 60usize),
                        (1744830467u32, 13usize),
                        (268435454u32, 61usize),
                        (1744830467u32, 14usize),
                        (268435454u32, 62usize),
                        (1744830467u32, 15usize),
                        (268435454u32, 63usize),
                        (1744830467u32, 16usize),
                        (268435454u32, 64usize),
                        (1744830467u32, 17usize),
                        (268435454u32, 65usize),
                        (1744830467u32, 18usize),
                        (268435454u32, 66usize),
                        (268435454u32, 69usize),
                        (268435454u32, 79usize),
                        (268435454u32, 80usize),
                        (268435454u32, 81usize),
                        (268435454u32, 82usize),
                        (268435454u32, 83usize),
                        (268435454u32, 84usize),
                        (268435454u32, 85usize),
                        (268435454u32, 86usize),
                        (268435454u32, 87usize),
                        (268435454u32, 88usize),
                        (268435454u32, 89usize),
                        (268435454u32, 90usize),
                        (268435454u32, 91usize),
                        (268435454u32, 92usize),
                        (268435454u32, 93usize),
                        (268435454u32, 94usize),
                        (1744830467u32, 67usize),
                        (1744830467u32, 19usize),
                        (65536u32, 20usize),
                        (1744830467u32, 20usize),
                        (65536u32, 21usize),
                        (1744830467u32, 21usize),
                        (65536u32, 22usize),
                        (1744830467u32, 22usize),
                        (65536u32, 23usize),
                        (1744830467u32, 23usize),
                        (65536u32, 24usize),
                        (1744830467u32, 24usize),
                        (65536u32, 25usize),
                        (1744830467u32, 25usize),
                        (65536u32, 26usize),
                        (1744830467u32, 26usize),
                        (65536u32, 27usize),
                        (1744830467u32, 27usize),
                        (65536u32, 28usize),
                        (1744830467u32, 28usize),
                        (65536u32, 29usize),
                        (1744830467u32, 29usize),
                        (65536u32, 30usize),
                        (1744830467u32, 30usize),
                        (65536u32, 31usize),
                        (1744830467u32, 31usize),
                        (65536u32, 32usize),
                        (1744830467u32, 32usize),
                        (65536u32, 33usize),
                        (1744830467u32, 33usize),
                        (65536u32, 34usize),
                        (1744830467u32, 34usize),
                        (65536u32, 35usize),
                        (1744830467u32, 20usize),
                        (65536u32, 21usize),
                        (1744830467u32, 21usize),
                        (65536u32, 22usize),
                        (1744830467u32, 22usize),
                        (65536u32, 23usize),
                        (1744830467u32, 23usize),
                        (65536u32, 24usize),
                        (1744830467u32, 24usize),
                        (65536u32, 25usize),
                        (1744830467u32, 25usize),
                        (65536u32, 26usize),
                        (1744830467u32, 26usize),
                        (65536u32, 27usize),
                        (1744830467u32, 27usize),
                        (65536u32, 28usize),
                        (1744830467u32, 28usize),
                        (65536u32, 29usize),
                        (1744830467u32, 29usize),
                        (65536u32, 30usize),
                        (1744830467u32, 30usize),
                        (65536u32, 31usize),
                        (1744830467u32, 31usize),
                        (65536u32, 32usize),
                        (1744830467u32, 32usize),
                        (65536u32, 33usize),
                        (1744830467u32, 33usize),
                        (65536u32, 34usize),
                        (1744830467u32, 34usize),
                        (65536u32, 35usize),
                        (1744830467u32, 35usize),
                        (65536u32, 36usize),
                        (1744830467u32, 21usize),
                        (65536u32, 22usize),
                        (1744830467u32, 22usize),
                        (65536u32, 23usize),
                        (1744830467u32, 23usize),
                        (65536u32, 24usize),
                        (1744830467u32, 24usize),
                        (65536u32, 25usize),
                        (1744830467u32, 25usize),
                        (65536u32, 26usize),
                        (1744830467u32, 26usize),
                        (65536u32, 27usize),
                        (1744830467u32, 27usize),
                        (65536u32, 28usize),
                        (1744830467u32, 28usize),
                        (65536u32, 29usize),
                        (1744830467u32, 29usize),
                        (65536u32, 30usize),
                        (1744830467u32, 30usize),
                        (65536u32, 31usize),
                        (1744830467u32, 31usize),
                        (65536u32, 32usize),
                        (1744830467u32, 32usize),
                        (65536u32, 33usize),
                        (1744830467u32, 33usize),
                        (65536u32, 34usize),
                        (1744830467u32, 34usize),
                        (65536u32, 35usize),
                        (1744830467u32, 35usize),
                        (65536u32, 36usize),
                        (1744830467u32, 36usize),
                        (65536u32, 37usize),
                        (1744830467u32, 22usize),
                        (65536u32, 23usize),
                        (1744830467u32, 23usize),
                        (65536u32, 24usize),
                        (1744830467u32, 24usize),
                        (65536u32, 25usize),
                        (1744830467u32, 25usize),
                        (65536u32, 26usize),
                        (1744830467u32, 26usize),
                        (65536u32, 27usize),
                        (1744830467u32, 27usize),
                        (65536u32, 28usize),
                        (1744830467u32, 28usize),
                        (65536u32, 29usize),
                        (1744830467u32, 29usize),
                        (65536u32, 30usize),
                        (1744830467u32, 30usize),
                        (65536u32, 31usize),
                        (1744830467u32, 31usize),
                        (65536u32, 32usize),
                        (1744830467u32, 32usize),
                        (65536u32, 33usize),
                        (1744830467u32, 33usize),
                        (65536u32, 34usize),
                        (1744830467u32, 34usize),
                        (65536u32, 35usize),
                        (1744830467u32, 35usize),
                        (65536u32, 36usize),
                        (1744830467u32, 36usize),
                        (65536u32, 37usize),
                        (1744830467u32, 37usize),
                        (65536u32, 38usize),
                        (1744830467u32, 23usize),
                        (65536u32, 24usize),
                        (1744830467u32, 24usize),
                        (65536u32, 25usize),
                        (1744830467u32, 25usize),
                        (65536u32, 26usize),
                        (1744830467u32, 26usize),
                        (65536u32, 27usize),
                        (1744830467u32, 27usize),
                        (65536u32, 28usize),
                        (1744830467u32, 28usize),
                        (65536u32, 29usize),
                        (1744830467u32, 29usize),
                        (65536u32, 30usize),
                        (1744830467u32, 30usize),
                        (65536u32, 31usize),
                        (1744830467u32, 31usize),
                        (65536u32, 32usize),
                        (1744830467u32, 32usize),
                        (65536u32, 33usize),
                        (1744830467u32, 33usize),
                        (65536u32, 34usize),
                        (1744830467u32, 34usize),
                        (65536u32, 35usize),
                        (1744830467u32, 35usize),
                        (65536u32, 36usize),
                        (1744830467u32, 36usize),
                        (65536u32, 37usize),
                        (1744830467u32, 37usize),
                        (65536u32, 38usize),
                        (1744830467u32, 38usize),
                        (65536u32, 39usize),
                        (1744830467u32, 24usize),
                        (65536u32, 25usize),
                        (1744830467u32, 25usize),
                        (65536u32, 26usize),
                        (1744830467u32, 26usize),
                        (65536u32, 27usize),
                        (1744830467u32, 27usize),
                        (65536u32, 28usize),
                        (1744830467u32, 28usize),
                        (65536u32, 29usize),
                        (1744830467u32, 29usize),
                        (65536u32, 30usize),
                        (1744830467u32, 30usize),
                        (65536u32, 31usize),
                        (1744830467u32, 31usize),
                        (65536u32, 32usize),
                        (1744830467u32, 32usize),
                        (65536u32, 33usize),
                        (1744830467u32, 33usize),
                        (65536u32, 34usize),
                        (1744830467u32, 34usize),
                        (65536u32, 35usize),
                        (1744830467u32, 35usize),
                        (65536u32, 36usize),
                        (1744830467u32, 36usize),
                        (65536u32, 37usize),
                        (1744830467u32, 37usize),
                        (65536u32, 38usize),
                        (1744830467u32, 38usize),
                        (65536u32, 39usize),
                        (1744830467u32, 39usize),
                        (65536u32, 40usize),
                        (1744830467u32, 25usize),
                        (65536u32, 26usize),
                        (1744830467u32, 26usize),
                        (65536u32, 27usize),
                        (1744830467u32, 27usize),
                        (65536u32, 28usize),
                        (1744830467u32, 28usize),
                        (65536u32, 29usize),
                        (1744830467u32, 29usize),
                        (65536u32, 30usize),
                        (1744830467u32, 30usize),
                        (65536u32, 31usize),
                        (1744830467u32, 31usize),
                        (65536u32, 32usize),
                        (1744830467u32, 32usize),
                        (65536u32, 33usize),
                        (1744830467u32, 33usize),
                        (65536u32, 34usize),
                        (1744830467u32, 34usize),
                        (65536u32, 35usize),
                        (1744830467u32, 35usize),
                        (65536u32, 36usize),
                        (1744830467u32, 36usize),
                        (65536u32, 37usize),
                        (1744830467u32, 37usize),
                        (65536u32, 38usize),
                        (1744830467u32, 38usize),
                        (65536u32, 39usize),
                        (1744830467u32, 39usize),
                        (65536u32, 40usize),
                        (1744830467u32, 40usize),
                        (65536u32, 41usize),
                        (1744830467u32, 26usize),
                        (65536u32, 27usize),
                        (1744830467u32, 27usize),
                        (65536u32, 28usize),
                        (1744830467u32, 28usize),
                        (65536u32, 29usize),
                        (1744830467u32, 29usize),
                        (65536u32, 30usize),
                        (1744830467u32, 30usize),
                        (65536u32, 31usize),
                        (1744830467u32, 31usize),
                        (65536u32, 32usize),
                        (1744830467u32, 32usize),
                        (65536u32, 33usize),
                        (1744830467u32, 33usize),
                        (65536u32, 34usize),
                        (1744830467u32, 34usize),
                        (65536u32, 35usize),
                        (1744830467u32, 35usize),
                        (65536u32, 36usize),
                        (1744830467u32, 36usize),
                        (65536u32, 37usize),
                        (1744830467u32, 37usize),
                        (65536u32, 38usize),
                        (1744830467u32, 38usize),
                        (65536u32, 39usize),
                        (1744830467u32, 39usize),
                        (65536u32, 40usize),
                        (1744830467u32, 40usize),
                        (65536u32, 41usize),
                        (1744830467u32, 41usize),
                        (65536u32, 42usize),
                        (1744830467u32, 27usize),
                        (65536u32, 28usize),
                        (1744830467u32, 28usize),
                        (65536u32, 29usize),
                        (1744830467u32, 29usize),
                        (65536u32, 30usize),
                        (1744830467u32, 30usize),
                        (65536u32, 31usize),
                        (1744830467u32, 31usize),
                        (65536u32, 32usize),
                        (1744830467u32, 32usize),
                        (65536u32, 33usize),
                        (1744830467u32, 33usize),
                        (65536u32, 34usize),
                        (1744830467u32, 34usize),
                        (65536u32, 35usize),
                        (1744830467u32, 35usize),
                        (65536u32, 36usize),
                        (1744830467u32, 36usize),
                        (65536u32, 37usize),
                        (1744830467u32, 37usize),
                        (65536u32, 38usize),
                        (1744830467u32, 38usize),
                        (65536u32, 39usize),
                        (1744830467u32, 39usize),
                        (65536u32, 40usize),
                        (1744830467u32, 40usize),
                        (65536u32, 41usize),
                        (1744830467u32, 41usize),
                        (65536u32, 42usize),
                        (1744830467u32, 42usize),
                        (65536u32, 43usize),
                        (1744830467u32, 28usize),
                        (65536u32, 29usize),
                        (1744830467u32, 29usize),
                        (65536u32, 30usize),
                        (1744830467u32, 30usize),
                        (65536u32, 31usize),
                        (1744830467u32, 31usize),
                        (65536u32, 32usize),
                        (1744830467u32, 32usize),
                        (65536u32, 33usize),
                        (1744830467u32, 33usize),
                        (65536u32, 34usize),
                        (1744830467u32, 34usize),
                        (65536u32, 35usize),
                        (1744830467u32, 35usize),
                        (65536u32, 36usize),
                        (1744830467u32, 36usize),
                        (65536u32, 37usize),
                        (1744830467u32, 37usize),
                        (65536u32, 38usize),
                        (1744830467u32, 38usize),
                        (65536u32, 39usize),
                        (1744830467u32, 39usize),
                        (65536u32, 40usize),
                        (1744830467u32, 40usize),
                        (65536u32, 41usize),
                        (1744830467u32, 41usize),
                        (65536u32, 42usize),
                        (1744830467u32, 42usize),
                        (65536u32, 43usize),
                        (1744830467u32, 43usize),
                        (65536u32, 44usize),
                        (1744830467u32, 29usize),
                        (65536u32, 30usize),
                        (1744830467u32, 30usize),
                        (65536u32, 31usize),
                        (1744830467u32, 31usize),
                        (65536u32, 32usize),
                        (1744830467u32, 32usize),
                        (65536u32, 33usize),
                        (1744830467u32, 33usize),
                        (65536u32, 34usize),
                        (1744830467u32, 34usize),
                        (65536u32, 35usize),
                        (1744830467u32, 35usize),
                        (65536u32, 36usize),
                        (1744830467u32, 36usize),
                        (65536u32, 37usize),
                        (1744830467u32, 37usize),
                        (65536u32, 38usize),
                        (1744830467u32, 38usize),
                        (65536u32, 39usize),
                        (1744830467u32, 39usize),
                        (65536u32, 40usize),
                        (1744830467u32, 40usize),
                        (65536u32, 41usize),
                        (1744830467u32, 41usize),
                        (65536u32, 42usize),
                        (1744830467u32, 42usize),
                        (65536u32, 43usize),
                        (1744830467u32, 43usize),
                        (65536u32, 44usize),
                        (1744830467u32, 44usize),
                        (65536u32, 45usize),
                        (1744830467u32, 30usize),
                        (65536u32, 31usize),
                        (1744830467u32, 31usize),
                        (65536u32, 32usize),
                        (1744830467u32, 32usize),
                        (65536u32, 33usize),
                        (1744830467u32, 33usize),
                        (65536u32, 34usize),
                        (1744830467u32, 34usize),
                        (65536u32, 35usize),
                        (1744830467u32, 35usize),
                        (65536u32, 36usize),
                        (1744830467u32, 36usize),
                        (65536u32, 37usize),
                        (1744830467u32, 37usize),
                        (65536u32, 38usize),
                        (1744830467u32, 38usize),
                        (65536u32, 39usize),
                        (1744830467u32, 39usize),
                        (65536u32, 40usize),
                        (1744830467u32, 40usize),
                        (65536u32, 41usize),
                        (1744830467u32, 41usize),
                        (65536u32, 42usize),
                        (1744830467u32, 42usize),
                        (65536u32, 43usize),
                        (1744830467u32, 43usize),
                        (65536u32, 44usize),
                        (1744830467u32, 44usize),
                        (65536u32, 45usize),
                        (1744830467u32, 45usize),
                        (65536u32, 46usize),
                        (1744830467u32, 31usize),
                        (65536u32, 32usize),
                        (1744830467u32, 32usize),
                        (65536u32, 33usize),
                        (1744830467u32, 33usize),
                        (65536u32, 34usize),
                        (1744830467u32, 34usize),
                        (65536u32, 35usize),
                        (1744830467u32, 35usize),
                        (65536u32, 36usize),
                        (1744830467u32, 36usize),
                        (65536u32, 37usize),
                        (1744830467u32, 37usize),
                        (65536u32, 38usize),
                        (1744830467u32, 38usize),
                        (65536u32, 39usize),
                        (1744830467u32, 39usize),
                        (65536u32, 40usize),
                        (1744830467u32, 40usize),
                        (65536u32, 41usize),
                        (1744830467u32, 41usize),
                        (65536u32, 42usize),
                        (1744830467u32, 42usize),
                        (65536u32, 43usize),
                        (1744830467u32, 43usize),
                        (65536u32, 44usize),
                        (1744830467u32, 44usize),
                        (65536u32, 45usize),
                        (1744830467u32, 45usize),
                        (65536u32, 46usize),
                        (1744830467u32, 46usize),
                        (65536u32, 47usize),
                        (1744830467u32, 32usize),
                        (65536u32, 33usize),
                        (1744830467u32, 33usize),
                        (65536u32, 34usize),
                        (1744830467u32, 34usize),
                        (65536u32, 35usize),
                        (1744830467u32, 35usize),
                        (65536u32, 36usize),
                        (1744830467u32, 36usize),
                        (65536u32, 37usize),
                        (1744830467u32, 37usize),
                        (65536u32, 38usize),
                        (1744830467u32, 38usize),
                        (65536u32, 39usize),
                        (1744830467u32, 39usize),
                        (65536u32, 40usize),
                        (1744830467u32, 40usize),
                        (65536u32, 41usize),
                        (1744830467u32, 41usize),
                        (65536u32, 42usize),
                        (1744830467u32, 42usize),
                        (65536u32, 43usize),
                        (1744830467u32, 43usize),
                        (65536u32, 44usize),
                        (1744830467u32, 44usize),
                        (65536u32, 45usize),
                        (1744830467u32, 45usize),
                        (65536u32, 46usize),
                        (1744830467u32, 46usize),
                        (65536u32, 47usize),
                        (1744830467u32, 47usize),
                        (65536u32, 48usize),
                        (1744830467u32, 33usize),
                        (65536u32, 34usize),
                        (1744830467u32, 34usize),
                        (65536u32, 35usize),
                        (1744830467u32, 35usize),
                        (65536u32, 36usize),
                        (1744830467u32, 36usize),
                        (65536u32, 37usize),
                        (1744830467u32, 37usize),
                        (65536u32, 38usize),
                        (1744830467u32, 38usize),
                        (65536u32, 39usize),
                        (1744830467u32, 39usize),
                        (65536u32, 40usize),
                        (1744830467u32, 40usize),
                        (65536u32, 41usize),
                        (1744830467u32, 41usize),
                        (65536u32, 42usize),
                        (1744830467u32, 42usize),
                        (65536u32, 43usize),
                        (1744830467u32, 43usize),
                        (65536u32, 44usize),
                        (1744830467u32, 44usize),
                        (65536u32, 45usize),
                        (1744830467u32, 45usize),
                        (65536u32, 46usize),
                        (1744830467u32, 46usize),
                        (65536u32, 47usize),
                        (1744830467u32, 47usize),
                        (65536u32, 48usize),
                        (1744830467u32, 48usize),
                        (65536u32, 49usize),
                        (1744830467u32, 34usize),
                        (65536u32, 35usize),
                        (1744830467u32, 35usize),
                        (65536u32, 36usize),
                        (1744830467u32, 36usize),
                        (65536u32, 37usize),
                        (1744830467u32, 37usize),
                        (65536u32, 38usize),
                        (1744830467u32, 38usize),
                        (65536u32, 39usize),
                        (1744830467u32, 39usize),
                        (65536u32, 40usize),
                        (1744830467u32, 40usize),
                        (65536u32, 41usize),
                        (1744830467u32, 41usize),
                        (65536u32, 42usize),
                        (1744830467u32, 42usize),
                        (65536u32, 43usize),
                        (1744830467u32, 43usize),
                        (65536u32, 44usize),
                        (1744830467u32, 44usize),
                        (65536u32, 45usize),
                        (1744830467u32, 45usize),
                        (65536u32, 46usize),
                        (1744830467u32, 46usize),
                        (65536u32, 47usize),
                        (1744830467u32, 47usize),
                        (65536u32, 48usize),
                        (1744830467u32, 48usize),
                        (65536u32, 49usize),
                        (1744830467u32, 49usize),
                        (65536u32, 50usize),
                        (268435454u32, 95usize),
                        (268435454u32, 96usize),
                        (268435454u32, 97usize),
                        (268435454u32, 98usize),
                        (268435454u32, 99usize),
                        (268435454u32, 100usize),
                        (268435454u32, 101usize),
                        (268435454u32, 102usize),
                        (268435454u32, 103usize),
                        (268435454u32, 104usize),
                        (268435454u32, 105usize),
                        (268435454u32, 106usize),
                        (268435454u32, 107usize),
                        (268435454u32, 108usize),
                        (268435454u32, 109usize),
                        (268435454u32, 110usize),
                        (268435454u32, 111usize),
                        (268435454u32, 112usize),
                        (268435454u32, 113usize),
                        (268435454u32, 114usize),
                        (268435454u32, 3usize),
                        (1744830467u32, 3usize),
                        (268435454u32, 3usize),
                        (1744830467u32, 3usize),
                        (268435454u32, 51usize),
                        (268435454u32, 19usize),
                        (2013200385u32, 20usize),
                        (268435454u32, 20usize),
                        (2013200385u32, 21usize),
                        (268435454u32, 21usize),
                        (2013200385u32, 22usize),
                        (268435454u32, 22usize),
                        (2013200385u32, 23usize),
                        (268435454u32, 23usize),
                        (2013200385u32, 24usize),
                        (268435454u32, 24usize),
                        (2013200385u32, 25usize),
                        (268435454u32, 25usize),
                        (2013200385u32, 26usize),
                        (268435454u32, 26usize),
                        (2013200385u32, 27usize),
                        (268435454u32, 27usize),
                        (2013200385u32, 28usize),
                        (268435454u32, 28usize),
                        (2013200385u32, 29usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (65536u32, 20usize),
                        (65536u32, 21usize),
                        (65536u32, 22usize),
                        (65536u32, 23usize),
                        (65536u32, 24usize),
                        (65536u32, 25usize),
                        (65536u32, 26usize),
                        (65536u32, 27usize),
                        (65536u32, 28usize),
                        (65536u32, 29usize),
                        (65536u32, 30usize),
                        (65536u32, 31usize),
                        (65536u32, 32usize),
                        (65536u32, 33usize),
                        (65536u32, 34usize),
                        (65536u32, 35usize),
                        (268435454u32, 4usize),
                        (1744830467u32, 4usize),
                        (268435454u32, 4usize),
                        (1744830467u32, 4usize),
                        (268435454u32, 52usize),
                        (268435454u32, 20usize),
                        (2013200385u32, 21usize),
                        (268435454u32, 21usize),
                        (2013200385u32, 22usize),
                        (268435454u32, 22usize),
                        (2013200385u32, 23usize),
                        (268435454u32, 23usize),
                        (2013200385u32, 24usize),
                        (268435454u32, 24usize),
                        (2013200385u32, 25usize),
                        (268435454u32, 25usize),
                        (2013200385u32, 26usize),
                        (268435454u32, 26usize),
                        (2013200385u32, 27usize),
                        (268435454u32, 27usize),
                        (2013200385u32, 28usize),
                        (268435454u32, 28usize),
                        (2013200385u32, 29usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (65536u32, 21usize),
                        (65536u32, 22usize),
                        (65536u32, 23usize),
                        (65536u32, 24usize),
                        (65536u32, 25usize),
                        (65536u32, 26usize),
                        (65536u32, 27usize),
                        (65536u32, 28usize),
                        (65536u32, 29usize),
                        (65536u32, 30usize),
                        (65536u32, 31usize),
                        (65536u32, 32usize),
                        (65536u32, 33usize),
                        (65536u32, 34usize),
                        (65536u32, 35usize),
                        (65536u32, 36usize),
                        (268435454u32, 5usize),
                        (1744830467u32, 5usize),
                        (268435454u32, 5usize),
                        (1744830467u32, 5usize),
                        (268435454u32, 53usize),
                        (268435454u32, 21usize),
                        (2013200385u32, 22usize),
                        (268435454u32, 22usize),
                        (2013200385u32, 23usize),
                        (268435454u32, 23usize),
                        (2013200385u32, 24usize),
                        (268435454u32, 24usize),
                        (2013200385u32, 25usize),
                        (268435454u32, 25usize),
                        (2013200385u32, 26usize),
                        (268435454u32, 26usize),
                        (2013200385u32, 27usize),
                        (268435454u32, 27usize),
                        (2013200385u32, 28usize),
                        (268435454u32, 28usize),
                        (2013200385u32, 29usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (65536u32, 22usize),
                        (65536u32, 23usize),
                        (65536u32, 24usize),
                        (65536u32, 25usize),
                        (65536u32, 26usize),
                        (65536u32, 27usize),
                        (65536u32, 28usize),
                        (65536u32, 29usize),
                        (65536u32, 30usize),
                        (65536u32, 31usize),
                        (65536u32, 32usize),
                        (65536u32, 33usize),
                        (65536u32, 34usize),
                        (65536u32, 35usize),
                        (65536u32, 36usize),
                        (65536u32, 37usize),
                        (268435454u32, 6usize),
                        (1744830467u32, 6usize),
                        (268435454u32, 6usize),
                        (1744830467u32, 6usize),
                        (268435454u32, 54usize),
                        (268435454u32, 22usize),
                        (2013200385u32, 23usize),
                        (268435454u32, 23usize),
                        (2013200385u32, 24usize),
                        (268435454u32, 24usize),
                        (2013200385u32, 25usize),
                        (268435454u32, 25usize),
                        (2013200385u32, 26usize),
                        (268435454u32, 26usize),
                        (2013200385u32, 27usize),
                        (268435454u32, 27usize),
                        (2013200385u32, 28usize),
                        (268435454u32, 28usize),
                        (2013200385u32, 29usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (65536u32, 23usize),
                        (65536u32, 24usize),
                        (65536u32, 25usize),
                        (65536u32, 26usize),
                        (65536u32, 27usize),
                        (65536u32, 28usize),
                        (65536u32, 29usize),
                        (65536u32, 30usize),
                        (65536u32, 31usize),
                        (65536u32, 32usize),
                        (65536u32, 33usize),
                        (65536u32, 34usize),
                        (65536u32, 35usize),
                        (65536u32, 36usize),
                        (65536u32, 37usize),
                        (65536u32, 38usize),
                        (268435454u32, 7usize),
                        (1744830467u32, 7usize),
                        (268435454u32, 7usize),
                        (1744830467u32, 7usize),
                        (268435454u32, 55usize),
                        (268435454u32, 23usize),
                        (2013200385u32, 24usize),
                        (268435454u32, 24usize),
                        (2013200385u32, 25usize),
                        (268435454u32, 25usize),
                        (2013200385u32, 26usize),
                        (268435454u32, 26usize),
                        (2013200385u32, 27usize),
                        (268435454u32, 27usize),
                        (2013200385u32, 28usize),
                        (268435454u32, 28usize),
                        (2013200385u32, 29usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (65536u32, 24usize),
                        (65536u32, 25usize),
                        (65536u32, 26usize),
                        (65536u32, 27usize),
                        (65536u32, 28usize),
                        (65536u32, 29usize),
                        (65536u32, 30usize),
                        (65536u32, 31usize),
                        (65536u32, 32usize),
                        (65536u32, 33usize),
                        (65536u32, 34usize),
                        (65536u32, 35usize),
                        (65536u32, 36usize),
                        (65536u32, 37usize),
                        (65536u32, 38usize),
                        (65536u32, 39usize),
                        (268435454u32, 8usize),
                        (1744830467u32, 8usize),
                        (268435454u32, 8usize),
                        (1744830467u32, 8usize),
                        (268435454u32, 56usize),
                        (268435454u32, 24usize),
                        (2013200385u32, 25usize),
                        (268435454u32, 25usize),
                        (2013200385u32, 26usize),
                        (268435454u32, 26usize),
                        (2013200385u32, 27usize),
                        (268435454u32, 27usize),
                        (2013200385u32, 28usize),
                        (268435454u32, 28usize),
                        (2013200385u32, 29usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (65536u32, 25usize),
                        (65536u32, 26usize),
                        (65536u32, 27usize),
                        (65536u32, 28usize),
                        (65536u32, 29usize),
                        (65536u32, 30usize),
                        (65536u32, 31usize),
                        (65536u32, 32usize),
                        (65536u32, 33usize),
                        (65536u32, 34usize),
                        (65536u32, 35usize),
                        (65536u32, 36usize),
                        (65536u32, 37usize),
                        (65536u32, 38usize),
                        (65536u32, 39usize),
                        (65536u32, 40usize),
                        (268435454u32, 9usize),
                        (1744830467u32, 9usize),
                        (268435454u32, 9usize),
                        (1744830467u32, 9usize),
                        (268435454u32, 57usize),
                        (268435454u32, 25usize),
                        (2013200385u32, 26usize),
                        (268435454u32, 26usize),
                        (2013200385u32, 27usize),
                        (268435454u32, 27usize),
                        (2013200385u32, 28usize),
                        (268435454u32, 28usize),
                        (2013200385u32, 29usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 40usize),
                        (2013200385u32, 41usize),
                        (65536u32, 26usize),
                        (65536u32, 27usize),
                        (65536u32, 28usize),
                        (65536u32, 29usize),
                        (65536u32, 30usize),
                        (65536u32, 31usize),
                        (65536u32, 32usize),
                        (65536u32, 33usize),
                        (65536u32, 34usize),
                        (65536u32, 35usize),
                        (65536u32, 36usize),
                        (65536u32, 37usize),
                        (65536u32, 38usize),
                        (65536u32, 39usize),
                        (65536u32, 40usize),
                        (65536u32, 41usize),
                        (268435454u32, 10usize),
                        (1744830467u32, 10usize),
                        (268435454u32, 10usize),
                        (1744830467u32, 10usize),
                        (268435454u32, 58usize),
                        (268435454u32, 26usize),
                        (2013200385u32, 27usize),
                        (268435454u32, 27usize),
                        (2013200385u32, 28usize),
                        (268435454u32, 28usize),
                        (2013200385u32, 29usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 40usize),
                        (2013200385u32, 41usize),
                        (268435454u32, 41usize),
                        (2013200385u32, 42usize),
                        (65536u32, 27usize),
                        (65536u32, 28usize),
                        (65536u32, 29usize),
                        (65536u32, 30usize),
                        (65536u32, 31usize),
                        (65536u32, 32usize),
                        (65536u32, 33usize),
                        (65536u32, 34usize),
                        (65536u32, 35usize),
                        (65536u32, 36usize),
                        (65536u32, 37usize),
                        (65536u32, 38usize),
                        (65536u32, 39usize),
                        (65536u32, 40usize),
                        (65536u32, 41usize),
                        (65536u32, 42usize),
                        (268435454u32, 11usize),
                        (1744830467u32, 11usize),
                        (268435454u32, 11usize),
                        (1744830467u32, 11usize),
                        (268435454u32, 59usize),
                        (268435454u32, 27usize),
                        (2013200385u32, 28usize),
                        (268435454u32, 28usize),
                        (2013200385u32, 29usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 40usize),
                        (2013200385u32, 41usize),
                        (268435454u32, 41usize),
                        (2013200385u32, 42usize),
                        (268435454u32, 42usize),
                        (2013200385u32, 43usize),
                        (65536u32, 28usize),
                        (65536u32, 29usize),
                        (65536u32, 30usize),
                        (65536u32, 31usize),
                        (65536u32, 32usize),
                        (65536u32, 33usize),
                        (65536u32, 34usize),
                        (65536u32, 35usize),
                        (65536u32, 36usize),
                        (65536u32, 37usize),
                        (65536u32, 38usize),
                        (65536u32, 39usize),
                        (65536u32, 40usize),
                        (65536u32, 41usize),
                        (65536u32, 42usize),
                        (65536u32, 43usize),
                        (268435454u32, 12usize),
                        (1744830467u32, 12usize),
                        (268435454u32, 12usize),
                        (1744830467u32, 12usize),
                        (268435454u32, 60usize),
                        (268435454u32, 28usize),
                        (2013200385u32, 29usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 40usize),
                        (2013200385u32, 41usize),
                        (268435454u32, 41usize),
                        (2013200385u32, 42usize),
                        (268435454u32, 42usize),
                        (2013200385u32, 43usize),
                        (268435454u32, 43usize),
                        (2013200385u32, 44usize),
                        (65536u32, 29usize),
                        (65536u32, 30usize),
                        (65536u32, 31usize),
                        (65536u32, 32usize),
                        (65536u32, 33usize),
                        (65536u32, 34usize),
                        (65536u32, 35usize),
                        (65536u32, 36usize),
                        (65536u32, 37usize),
                        (65536u32, 38usize),
                        (65536u32, 39usize),
                        (65536u32, 40usize),
                        (65536u32, 41usize),
                        (65536u32, 42usize),
                        (65536u32, 43usize),
                        (65536u32, 44usize),
                        (268435454u32, 13usize),
                        (1744830467u32, 13usize),
                        (268435454u32, 13usize),
                        (1744830467u32, 13usize),
                        (268435454u32, 61usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 40usize),
                        (2013200385u32, 41usize),
                        (268435454u32, 41usize),
                        (2013200385u32, 42usize),
                        (268435454u32, 42usize),
                        (2013200385u32, 43usize),
                        (268435454u32, 43usize),
                        (2013200385u32, 44usize),
                        (268435454u32, 44usize),
                        (2013200385u32, 45usize),
                        (65536u32, 30usize),
                        (65536u32, 31usize),
                        (65536u32, 32usize),
                        (65536u32, 33usize),
                        (65536u32, 34usize),
                        (65536u32, 35usize),
                        (65536u32, 36usize),
                        (65536u32, 37usize),
                        (65536u32, 38usize),
                        (65536u32, 39usize),
                        (65536u32, 40usize),
                        (65536u32, 41usize),
                        (65536u32, 42usize),
                        (65536u32, 43usize),
                        (65536u32, 44usize),
                        (65536u32, 45usize),
                        (268435454u32, 14usize),
                        (1744830467u32, 14usize),
                        (268435454u32, 14usize),
                        (1744830467u32, 14usize),
                        (268435454u32, 62usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 40usize),
                        (2013200385u32, 41usize),
                        (268435454u32, 41usize),
                        (2013200385u32, 42usize),
                        (268435454u32, 42usize),
                        (2013200385u32, 43usize),
                        (268435454u32, 43usize),
                        (2013200385u32, 44usize),
                        (268435454u32, 44usize),
                        (2013200385u32, 45usize),
                        (268435454u32, 45usize),
                        (2013200385u32, 46usize),
                        (65536u32, 31usize),
                        (65536u32, 32usize),
                        (65536u32, 33usize),
                        (65536u32, 34usize),
                        (65536u32, 35usize),
                        (65536u32, 36usize),
                        (65536u32, 37usize),
                        (65536u32, 38usize),
                        (65536u32, 39usize),
                        (65536u32, 40usize),
                        (65536u32, 41usize),
                        (65536u32, 42usize),
                        (65536u32, 43usize),
                        (65536u32, 44usize),
                        (65536u32, 45usize),
                        (65536u32, 46usize),
                        (268435454u32, 15usize),
                        (1744830467u32, 15usize),
                        (268435454u32, 15usize),
                        (1744830467u32, 15usize),
                        (268435454u32, 63usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 40usize),
                        (2013200385u32, 41usize),
                        (268435454u32, 41usize),
                        (2013200385u32, 42usize),
                        (268435454u32, 42usize),
                        (2013200385u32, 43usize),
                        (268435454u32, 43usize),
                        (2013200385u32, 44usize),
                        (268435454u32, 44usize),
                        (2013200385u32, 45usize),
                        (268435454u32, 45usize),
                        (2013200385u32, 46usize),
                        (268435454u32, 46usize),
                        (2013200385u32, 47usize),
                        (65536u32, 32usize),
                        (65536u32, 33usize),
                        (65536u32, 34usize),
                        (65536u32, 35usize),
                        (65536u32, 36usize),
                        (65536u32, 37usize),
                        (65536u32, 38usize),
                        (65536u32, 39usize),
                        (65536u32, 40usize),
                        (65536u32, 41usize),
                        (65536u32, 42usize),
                        (65536u32, 43usize),
                        (65536u32, 44usize),
                        (65536u32, 45usize),
                        (65536u32, 46usize),
                        (65536u32, 47usize),
                        (268435454u32, 16usize),
                        (1744830467u32, 16usize),
                        (268435454u32, 16usize),
                        (1744830467u32, 16usize),
                        (268435454u32, 64usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 40usize),
                        (2013200385u32, 41usize),
                        (268435454u32, 41usize),
                        (2013200385u32, 42usize),
                        (268435454u32, 42usize),
                        (2013200385u32, 43usize),
                        (268435454u32, 43usize),
                        (2013200385u32, 44usize),
                        (268435454u32, 44usize),
                        (2013200385u32, 45usize),
                        (268435454u32, 45usize),
                        (2013200385u32, 46usize),
                        (268435454u32, 46usize),
                        (2013200385u32, 47usize),
                        (268435454u32, 47usize),
                        (2013200385u32, 48usize),
                        (65536u32, 33usize),
                        (65536u32, 34usize),
                        (65536u32, 35usize),
                        (65536u32, 36usize),
                        (65536u32, 37usize),
                        (65536u32, 38usize),
                        (65536u32, 39usize),
                        (65536u32, 40usize),
                        (65536u32, 41usize),
                        (65536u32, 42usize),
                        (65536u32, 43usize),
                        (65536u32, 44usize),
                        (65536u32, 45usize),
                        (65536u32, 46usize),
                        (65536u32, 47usize),
                        (65536u32, 48usize),
                        (268435454u32, 17usize),
                        (1744830467u32, 17usize),
                        (268435454u32, 17usize),
                        (1744830467u32, 17usize),
                        (268435454u32, 65usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 40usize),
                        (2013200385u32, 41usize),
                        (268435454u32, 41usize),
                        (2013200385u32, 42usize),
                        (268435454u32, 42usize),
                        (2013200385u32, 43usize),
                        (268435454u32, 43usize),
                        (2013200385u32, 44usize),
                        (268435454u32, 44usize),
                        (2013200385u32, 45usize),
                        (268435454u32, 45usize),
                        (2013200385u32, 46usize),
                        (268435454u32, 46usize),
                        (2013200385u32, 47usize),
                        (268435454u32, 47usize),
                        (2013200385u32, 48usize),
                        (268435454u32, 48usize),
                        (2013200385u32, 49usize),
                        (65536u32, 34usize),
                        (65536u32, 35usize),
                        (65536u32, 36usize),
                        (65536u32, 37usize),
                        (65536u32, 38usize),
                        (65536u32, 39usize),
                        (65536u32, 40usize),
                        (65536u32, 41usize),
                        (65536u32, 42usize),
                        (65536u32, 43usize),
                        (65536u32, 44usize),
                        (65536u32, 45usize),
                        (65536u32, 46usize),
                        (65536u32, 47usize),
                        (65536u32, 48usize),
                        (65536u32, 49usize),
                        (268435454u32, 18usize),
                        (1744830467u32, 18usize),
                        (268435454u32, 18usize),
                        (1744830467u32, 18usize),
                        (268435454u32, 66usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 40usize),
                        (2013200385u32, 41usize),
                        (268435454u32, 41usize),
                        (2013200385u32, 42usize),
                        (268435454u32, 42usize),
                        (2013200385u32, 43usize),
                        (268435454u32, 43usize),
                        (2013200385u32, 44usize),
                        (268435454u32, 44usize),
                        (2013200385u32, 45usize),
                        (268435454u32, 45usize),
                        (2013200385u32, 46usize),
                        (268435454u32, 46usize),
                        (2013200385u32, 47usize),
                        (268435454u32, 47usize),
                        (2013200385u32, 48usize),
                        (268435454u32, 48usize),
                        (2013200385u32, 49usize),
                        (268435454u32, 49usize),
                        (2013200385u32, 50usize),
                        (65536u32, 35usize),
                        (65536u32, 36usize),
                        (65536u32, 37usize),
                        (65536u32, 38usize),
                        (65536u32, 39usize),
                        (65536u32, 40usize),
                        (65536u32, 41usize),
                        (65536u32, 42usize),
                        (65536u32, 43usize),
                        (65536u32, 44usize),
                        (65536u32, 45usize),
                        (65536u32, 46usize),
                        (65536u32, 47usize),
                        (65536u32, 48usize),
                        (65536u32, 49usize),
                        (65536u32, 50usize),
                        (268435454u32, 3usize),
                        (268435454u32, 3usize),
                        (1744830467u32, 3usize),
                        (268435454u32, 3usize),
                        (268435454u32, 3usize),
                        (268435454u32, 19usize),
                        (2013200385u32, 20usize),
                        (268435454u32, 20usize),
                        (2013200385u32, 21usize),
                        (268435454u32, 21usize),
                        (2013200385u32, 22usize),
                        (268435454u32, 22usize),
                        (2013200385u32, 23usize),
                        (268435454u32, 23usize),
                        (2013200385u32, 24usize),
                        (268435454u32, 24usize),
                        (2013200385u32, 25usize),
                        (268435454u32, 25usize),
                        (2013200385u32, 26usize),
                        (268435454u32, 26usize),
                        (2013200385u32, 27usize),
                        (268435454u32, 27usize),
                        (2013200385u32, 28usize),
                        (268435454u32, 28usize),
                        (2013200385u32, 29usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 4usize),
                        (268435454u32, 4usize),
                        (1744830467u32, 4usize),
                        (268435454u32, 4usize),
                        (268435454u32, 4usize),
                        (268435454u32, 20usize),
                        (2013200385u32, 21usize),
                        (268435454u32, 21usize),
                        (2013200385u32, 22usize),
                        (268435454u32, 22usize),
                        (2013200385u32, 23usize),
                        (268435454u32, 23usize),
                        (2013200385u32, 24usize),
                        (268435454u32, 24usize),
                        (2013200385u32, 25usize),
                        (268435454u32, 25usize),
                        (2013200385u32, 26usize),
                        (268435454u32, 26usize),
                        (2013200385u32, 27usize),
                        (268435454u32, 27usize),
                        (2013200385u32, 28usize),
                        (268435454u32, 28usize),
                        (2013200385u32, 29usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 5usize),
                        (268435454u32, 5usize),
                        (1744830467u32, 5usize),
                        (268435454u32, 5usize),
                        (268435454u32, 5usize),
                        (268435454u32, 21usize),
                        (2013200385u32, 22usize),
                        (268435454u32, 22usize),
                        (2013200385u32, 23usize),
                        (268435454u32, 23usize),
                        (2013200385u32, 24usize),
                        (268435454u32, 24usize),
                        (2013200385u32, 25usize),
                        (268435454u32, 25usize),
                        (2013200385u32, 26usize),
                        (268435454u32, 26usize),
                        (2013200385u32, 27usize),
                        (268435454u32, 27usize),
                        (2013200385u32, 28usize),
                        (268435454u32, 28usize),
                        (2013200385u32, 29usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 6usize),
                        (268435454u32, 6usize),
                        (1744830467u32, 6usize),
                        (268435454u32, 6usize),
                        (268435454u32, 6usize),
                        (268435454u32, 22usize),
                        (2013200385u32, 23usize),
                        (268435454u32, 23usize),
                        (2013200385u32, 24usize),
                        (268435454u32, 24usize),
                        (2013200385u32, 25usize),
                        (268435454u32, 25usize),
                        (2013200385u32, 26usize),
                        (268435454u32, 26usize),
                        (2013200385u32, 27usize),
                        (268435454u32, 27usize),
                        (2013200385u32, 28usize),
                        (268435454u32, 28usize),
                        (2013200385u32, 29usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 7usize),
                        (268435454u32, 7usize),
                        (1744830467u32, 7usize),
                        (268435454u32, 7usize),
                        (268435454u32, 7usize),
                        (268435454u32, 23usize),
                        (2013200385u32, 24usize),
                        (268435454u32, 24usize),
                        (2013200385u32, 25usize),
                        (268435454u32, 25usize),
                        (2013200385u32, 26usize),
                        (268435454u32, 26usize),
                        (2013200385u32, 27usize),
                        (268435454u32, 27usize),
                        (2013200385u32, 28usize),
                        (268435454u32, 28usize),
                        (2013200385u32, 29usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 8usize),
                        (268435454u32, 8usize),
                        (1744830467u32, 8usize),
                        (268435454u32, 8usize),
                        (268435454u32, 8usize),
                        (268435454u32, 24usize),
                        (2013200385u32, 25usize),
                        (268435454u32, 25usize),
                        (2013200385u32, 26usize),
                        (268435454u32, 26usize),
                        (2013200385u32, 27usize),
                        (268435454u32, 27usize),
                        (2013200385u32, 28usize),
                        (268435454u32, 28usize),
                        (2013200385u32, 29usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 9usize),
                        (268435454u32, 9usize),
                        (1744830467u32, 9usize),
                        (268435454u32, 9usize),
                        (268435454u32, 9usize),
                        (268435454u32, 25usize),
                        (2013200385u32, 26usize),
                        (268435454u32, 26usize),
                        (2013200385u32, 27usize),
                        (268435454u32, 27usize),
                        (2013200385u32, 28usize),
                        (268435454u32, 28usize),
                        (2013200385u32, 29usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 40usize),
                        (2013200385u32, 41usize),
                        (268435454u32, 10usize),
                        (268435454u32, 10usize),
                        (1744830467u32, 10usize),
                        (268435454u32, 10usize),
                        (268435454u32, 10usize),
                        (268435454u32, 26usize),
                        (2013200385u32, 27usize),
                        (268435454u32, 27usize),
                        (2013200385u32, 28usize),
                        (268435454u32, 28usize),
                        (2013200385u32, 29usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 40usize),
                        (2013200385u32, 41usize),
                        (268435454u32, 41usize),
                        (2013200385u32, 42usize),
                        (268435454u32, 11usize),
                        (268435454u32, 11usize),
                        (1744830467u32, 11usize),
                        (268435454u32, 11usize),
                        (268435454u32, 11usize),
                        (268435454u32, 27usize),
                        (2013200385u32, 28usize),
                        (268435454u32, 28usize),
                        (2013200385u32, 29usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 40usize),
                        (2013200385u32, 41usize),
                        (268435454u32, 41usize),
                        (2013200385u32, 42usize),
                        (268435454u32, 42usize),
                        (2013200385u32, 43usize),
                        (268435454u32, 12usize),
                        (268435454u32, 12usize),
                        (1744830467u32, 12usize),
                        (268435454u32, 12usize),
                        (268435454u32, 12usize),
                        (268435454u32, 28usize),
                        (2013200385u32, 29usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 40usize),
                        (2013200385u32, 41usize),
                        (268435454u32, 41usize),
                        (2013200385u32, 42usize),
                        (268435454u32, 42usize),
                        (2013200385u32, 43usize),
                        (268435454u32, 43usize),
                        (2013200385u32, 44usize),
                        (268435454u32, 13usize),
                        (268435454u32, 13usize),
                        (1744830467u32, 13usize),
                        (268435454u32, 13usize),
                        (268435454u32, 13usize),
                        (268435454u32, 29usize),
                        (2013200385u32, 30usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 40usize),
                        (2013200385u32, 41usize),
                        (268435454u32, 41usize),
                        (2013200385u32, 42usize),
                        (268435454u32, 42usize),
                        (2013200385u32, 43usize),
                        (268435454u32, 43usize),
                        (2013200385u32, 44usize),
                        (268435454u32, 44usize),
                        (2013200385u32, 45usize),
                        (268435454u32, 14usize),
                        (268435454u32, 14usize),
                        (1744830467u32, 14usize),
                        (268435454u32, 14usize),
                        (268435454u32, 14usize),
                        (268435454u32, 30usize),
                        (2013200385u32, 31usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 40usize),
                        (2013200385u32, 41usize),
                        (268435454u32, 41usize),
                        (2013200385u32, 42usize),
                        (268435454u32, 42usize),
                        (2013200385u32, 43usize),
                        (268435454u32, 43usize),
                        (2013200385u32, 44usize),
                        (268435454u32, 44usize),
                        (2013200385u32, 45usize),
                        (268435454u32, 45usize),
                        (2013200385u32, 46usize),
                        (268435454u32, 15usize),
                        (268435454u32, 15usize),
                        (1744830467u32, 15usize),
                        (268435454u32, 15usize),
                        (268435454u32, 15usize),
                        (268435454u32, 31usize),
                        (2013200385u32, 32usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 40usize),
                        (2013200385u32, 41usize),
                        (268435454u32, 41usize),
                        (2013200385u32, 42usize),
                        (268435454u32, 42usize),
                        (2013200385u32, 43usize),
                        (268435454u32, 43usize),
                        (2013200385u32, 44usize),
                        (268435454u32, 44usize),
                        (2013200385u32, 45usize),
                        (268435454u32, 45usize),
                        (2013200385u32, 46usize),
                        (268435454u32, 46usize),
                        (2013200385u32, 47usize),
                        (268435454u32, 16usize),
                        (268435454u32, 16usize),
                        (1744830467u32, 16usize),
                        (268435454u32, 16usize),
                        (268435454u32, 16usize),
                        (268435454u32, 32usize),
                        (2013200385u32, 33usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 40usize),
                        (2013200385u32, 41usize),
                        (268435454u32, 41usize),
                        (2013200385u32, 42usize),
                        (268435454u32, 42usize),
                        (2013200385u32, 43usize),
                        (268435454u32, 43usize),
                        (2013200385u32, 44usize),
                        (268435454u32, 44usize),
                        (2013200385u32, 45usize),
                        (268435454u32, 45usize),
                        (2013200385u32, 46usize),
                        (268435454u32, 46usize),
                        (2013200385u32, 47usize),
                        (268435454u32, 47usize),
                        (2013200385u32, 48usize),
                        (268435454u32, 17usize),
                        (268435454u32, 17usize),
                        (1744830467u32, 17usize),
                        (268435454u32, 17usize),
                        (268435454u32, 17usize),
                        (268435454u32, 33usize),
                        (2013200385u32, 34usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 40usize),
                        (2013200385u32, 41usize),
                        (268435454u32, 41usize),
                        (2013200385u32, 42usize),
                        (268435454u32, 42usize),
                        (2013200385u32, 43usize),
                        (268435454u32, 43usize),
                        (2013200385u32, 44usize),
                        (268435454u32, 44usize),
                        (2013200385u32, 45usize),
                        (268435454u32, 45usize),
                        (2013200385u32, 46usize),
                        (268435454u32, 46usize),
                        (2013200385u32, 47usize),
                        (268435454u32, 47usize),
                        (2013200385u32, 48usize),
                        (268435454u32, 48usize),
                        (2013200385u32, 49usize),
                        (268435454u32, 18usize),
                        (268435454u32, 18usize),
                        (1744830467u32, 18usize),
                        (268435454u32, 18usize),
                        (268435454u32, 18usize),
                        (268435454u32, 34usize),
                        (2013200385u32, 35usize),
                        (268435454u32, 35usize),
                        (2013200385u32, 36usize),
                        (268435454u32, 36usize),
                        (2013200385u32, 37usize),
                        (268435454u32, 37usize),
                        (2013200385u32, 38usize),
                        (268435454u32, 38usize),
                        (2013200385u32, 39usize),
                        (268435454u32, 39usize),
                        (2013200385u32, 40usize),
                        (268435454u32, 40usize),
                        (2013200385u32, 41usize),
                        (268435454u32, 41usize),
                        (2013200385u32, 42usize),
                        (268435454u32, 42usize),
                        (2013200385u32, 43usize),
                        (268435454u32, 43usize),
                        (2013200385u32, 44usize),
                        (268435454u32, 44usize),
                        (2013200385u32, 45usize),
                        (268435454u32, 45usize),
                        (2013200385u32, 46usize),
                        (268435454u32, 46usize),
                        (2013200385u32, 47usize),
                        (268435454u32, 47usize),
                        (2013200385u32, 48usize),
                        (268435454u32, 48usize),
                        (2013200385u32, 49usize),
                        (268435454u32, 49usize),
                        (2013200385u32, 50usize),
                        (268435454u32, 0usize),
                    ];
                    let mut _g: usize = 0;
                    while _g < 1358usize {
                        let (idx_a, idx_b, term_start, term_count) = CK_QUAD_GROUPS[_g];
                        let va = evals.get_unchecked(idx_a)[j];
                        let vb = evals.get_unchecked(idx_b)[j];
                        let mut prod = va;
                        field_ops::mul_assign(&mut prod, &vb);
                        let mut _t: usize = 0;
                        while _t < term_count {
                            let (coeff, pow) = CK_QUAD_TERMS[term_start + _t];
                            let mut t: BabyBearExt4 = *challenge_powers.get_unchecked(pow);
                            field_ops::mul_assign_by_base(
                                &mut t,
                                &BabyBearField::from_reduced_raw_repr(coeff),
                            );
                            field_ops::mul_assign(&mut t, &prod);
                            field_ops::add_assign(&mut result, &t);
                            _t += 1;
                        }
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
        const SIMPLE_GATES: [(usize, [usize; 4]); 54usize] = [
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
            (5usize, [21usize, 22usize, 0usize, 0usize]),
            (5usize, [23usize, 24usize, 0usize, 0usize]),
            (5usize, [25usize, 26usize, 0usize, 0usize]),
            (5usize, [27usize, 28usize, 0usize, 0usize]),
            (5usize, [29usize, 30usize, 0usize, 0usize]),
            (5usize, [31usize, 32usize, 0usize, 0usize]),
            (5usize, [33usize, 34usize, 0usize, 0usize]),
            (5usize, [35usize, 36usize, 0usize, 0usize]),
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
                    const CK_CONST: [(u32, usize); 1usize] = [(1744830467u32, 1usize)];
                    let mut _i: usize = 0;
                    while _i < 1usize {
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
                    const CK_LIN: [(u32, usize, usize); 1usize] = [(268435454u32, 1usize, 39usize)];
                    let mut _i: usize = 0;
                    while _i < 1usize {
                        let (coeff, pow, eval_idx) = CK_LIN[_i];
                        let val = evals.get_unchecked(eval_idx)[j];
                        let mut t: BabyBearExt4 = *challenge_powers.get_unchecked(pow);
                        field_ops::mul_assign_by_base(
                            &mut t,
                            &BabyBearField::from_reduced_raw_repr(coeff),
                        );
                        field_ops::mul_assign(&mut t, &val);
                        field_ops::add_assign(&mut result, &t);
                        _i += 1;
                    }
                }
                {
                    const CK_QUAD_GROUPS: [(usize, usize, usize, usize); 2usize] = [
                        (37usize, 38usize, 0usize, 1usize),
                        (37usize, 39usize, 1usize, 1usize),
                    ];
                    const CK_QUAD_TERMS: [(u32, usize); 2usize] =
                        [(268435454u32, 1usize), (268435454u32, 0usize)];
                    let mut _g: usize = 0;
                    while _g < 2usize {
                        let (idx_a, idx_b, term_start, term_count) = CK_QUAD_GROUPS[_g];
                        let va = evals.get_unchecked(idx_a)[j];
                        let vb = evals.get_unchecked(idx_b)[j];
                        let mut prod = va;
                        field_ops::mul_assign(&mut prod, &vb);
                        let mut _t: usize = 0;
                        while _t < term_count {
                            let (coeff, pow) = CK_QUAD_TERMS[term_start + _t];
                            let mut t: BabyBearExt4 = *challenge_powers.get_unchecked(pow);
                            field_ops::mul_assign_by_base(
                                &mut t,
                                &BabyBearField::from_reduced_raw_repr(coeff),
                            );
                            field_ops::mul_assign(&mut t, &prod);
                            field_ops::add_assign(&mut result, &t);
                            _t += 1;
                        }
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
unsafe fn dim_reducing_6_final_step_accumulator(
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
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
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
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
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
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
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
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
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
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
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
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
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
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
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
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
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
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
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
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
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
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
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
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
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
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
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
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
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
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
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
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
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
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
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
    {
        let bc0 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let bc1 = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let v0 = unsafe { evals.get_unchecked(6usize) };
        let v1 = unsafe { evals.get_unchecked(7usize) };
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
pub fn verify_gkr_sumcheck<I: NonDeterminismSource>() -> Result<
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
            evals_flat.set_len(128usize);
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
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                dim_reducing_22_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 4usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    22usize,
                )?;
            let mut fc_len = 4usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                dim_reducing_21_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 5usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    21usize,
                )?;
            let mut fc_len = 5usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                dim_reducing_20_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 6usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    20usize,
                )?;
            let mut fc_len = 6usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                dim_reducing_19_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 7usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    19usize,
                )?;
            let mut fc_len = 7usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                dim_reducing_18_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 8usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    18usize,
                )?;
            let mut fc_len = 8usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                dim_reducing_17_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 9usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    17usize,
                )?;
            let mut fc_len = 9usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                dim_reducing_16_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 10usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    16usize,
                )?;
            let mut fc_len = 10usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                dim_reducing_15_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 11usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    15usize,
                )?;
            let mut fc_len = 11usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                dim_reducing_14_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 12usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    14usize,
                )?;
            let mut fc_len = 12usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                dim_reducing_13_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 13usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    13usize,
                )?;
            let mut fc_len = 13usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                dim_reducing_12_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 14usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    12usize,
                )?;
            let mut fc_len = 14usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                dim_reducing_11_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 15usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    11usize,
                )?;
            let mut fc_len = 15usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                dim_reducing_10_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 16usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    10usize,
                )?;
            let mut fc_len = 16usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                dim_reducing_9_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 17usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    9usize,
                )?;
            let mut fc_len = 17usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                dim_reducing_8_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 18usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    8usize,
                )?;
            let mut fc_len = 18usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                dim_reducing_7_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 19usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    7usize,
                )?;
            let mut fc_len = 19usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                dim_reducing_6_compute_claim(&state.prev_claims, state.batching_challenge);
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, 20usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    6usize,
                )?;
            let mut fc_len = 20usize;
            let data_words = 8usize * 4 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 4]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 8usize);
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
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    5usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 15usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 2]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 15usize);
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
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    4usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 27usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 2]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 27usize);
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
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    3usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 49usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 2]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 49usize);
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
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    2usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 91usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 2]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 91usize);
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
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    1usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 160usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 2]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 160usize);
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
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    0usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 357usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            read_eval_data_from_nds::<I, GKR_EVAL_BUF>(&mut eval_buf, data_words);
            {
                let evals: &[[BabyBearExt4; 2]] =
                    eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 357usize);
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
            let mut extra_evals = LazyVec::<BabyBearExt4, 46usize>::new();
            unsafe {
                extra_evals.set_len(46usize);
            }
            read_field_els::<I>(extra_evals.as_mut_slice());
            commit_field_els(&mut seed, extra_evals.as_slice());
            let final_step_evals: &[[BabyBearExt4; 2]] =
                eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, 357usize);
            state.prev_claims.clear();
            {
                const EXTRA_POS: [(usize, usize); 46usize] = [
                    (161usize, 0usize),
                    (162usize, 1usize),
                    (163usize, 2usize),
                    (164usize, 3usize),
                    (165usize, 4usize),
                    (166usize, 5usize),
                    (171usize, 6usize),
                    (172usize, 7usize),
                    (177usize, 8usize),
                    (178usize, 9usize),
                    (183usize, 10usize),
                    (184usize, 11usize),
                    (189usize, 12usize),
                    (190usize, 13usize),
                    (195usize, 14usize),
                    (196usize, 15usize),
                    (201usize, 16usize),
                    (202usize, 17usize),
                    (207usize, 18usize),
                    (208usize, 19usize),
                    (213usize, 20usize),
                    (214usize, 21usize),
                    (215usize, 22usize),
                    (216usize, 23usize),
                    (217usize, 24usize),
                    (218usize, 25usize),
                    (221usize, 26usize),
                    (222usize, 27usize),
                    (225usize, 28usize),
                    (226usize, 29usize),
                    (229usize, 30usize),
                    (230usize, 31usize),
                    (233usize, 32usize),
                    (234usize, 33usize),
                    (237usize, 34usize),
                    (238usize, 35usize),
                    (241usize, 36usize),
                    (242usize, 37usize),
                    (245usize, 38usize),
                    (246usize, 39usize),
                    (249usize, 40usize),
                    (250usize, 41usize),
                    (252usize, 42usize),
                    (260usize, 43usize),
                    (261usize, 44usize),
                    (262usize, 45usize),
                ];
                let mut regular_idx: usize = 0;
                let mut ep_idx: usize = 0;
                let mut merged_idx: usize = 0;
                while merged_idx < 403usize {
                    if ep_idx < 46usize && EXTRA_POS[ep_idx].0 == merged_idx {
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
                const SC_DESCS: [(usize, u32, usize, usize); 38usize] = [
                    (303usize, 1476395013u32, 0usize, 3usize),
                    (304usize, 133099247u32, 3usize, 3usize),
                    (305usize, 1476395013u32, 6usize, 3usize),
                    (306usize, 133099247u32, 9usize, 3usize),
                    (307usize, 1476395013u32, 12usize, 3usize),
                    (308usize, 133099247u32, 15usize, 3usize),
                    (309usize, 1476395013u32, 18usize, 3usize),
                    (310usize, 133099247u32, 21usize, 3usize),
                    (311usize, 1476395013u32, 24usize, 3usize),
                    (312usize, 133099247u32, 27usize, 3usize),
                    (313usize, 1476395013u32, 30usize, 3usize),
                    (314usize, 133099247u32, 33usize, 3usize),
                    (315usize, 1476395013u32, 36usize, 3usize),
                    (316usize, 133099247u32, 39usize, 3usize),
                    (317usize, 1476395013u32, 42usize, 3usize),
                    (318usize, 133099247u32, 45usize, 3usize),
                    (319usize, 1476395013u32, 48usize, 3usize),
                    (320usize, 133099247u32, 51usize, 3usize),
                    (321usize, 1476395013u32, 54usize, 3usize),
                    (322usize, 133099247u32, 57usize, 3usize),
                    (323usize, 1476395013u32, 60usize, 3usize),
                    (324usize, 133099247u32, 63usize, 3usize),
                    (325usize, 1476395013u32, 66usize, 3usize),
                    (326usize, 133099247u32, 69usize, 3usize),
                    (327usize, 1476395013u32, 72usize, 3usize),
                    (328usize, 133099247u32, 75usize, 3usize),
                    (329usize, 1476395013u32, 78usize, 3usize),
                    (330usize, 133099247u32, 81usize, 3usize),
                    (331usize, 1476395013u32, 84usize, 3usize),
                    (332usize, 133099247u32, 87usize, 3usize),
                    (333usize, 1476395013u32, 90usize, 3usize),
                    (334usize, 133099247u32, 93usize, 3usize),
                    (335usize, 1476395013u32, 96usize, 3usize),
                    (336usize, 133099247u32, 99usize, 3usize),
                    (337usize, 1476395013u32, 102usize, 3usize),
                    (338usize, 133099247u32, 105usize, 3usize),
                    (339usize, 1476395013u32, 108usize, 3usize),
                    (340usize, 133099247u32, 111usize, 3usize),
                ];
                const SC_TERMS: [(u32, usize); 114usize] = [
                    (1744830467u32, 256usize),
                    (268435454u32, 161usize),
                    (133099247u32, 139usize),
                    (1744830467u32, 257usize),
                    (268435454u32, 162usize),
                    (1744830467u32, 139usize),
                    (1744830467u32, 256usize),
                    (268435454u32, 165usize),
                    (133099247u32, 140usize),
                    (1744830467u32, 257usize),
                    (268435454u32, 166usize),
                    (1744830467u32, 140usize),
                    (1744830467u32, 256usize),
                    (268435454u32, 171usize),
                    (133099247u32, 141usize),
                    (1744830467u32, 257usize),
                    (268435454u32, 172usize),
                    (1744830467u32, 141usize),
                    (1744830467u32, 256usize),
                    (268435454u32, 177usize),
                    (133099247u32, 142usize),
                    (1744830467u32, 257usize),
                    (268435454u32, 178usize),
                    (1744830467u32, 142usize),
                    (1744830467u32, 256usize),
                    (268435454u32, 183usize),
                    (133099247u32, 143usize),
                    (1744830467u32, 257usize),
                    (268435454u32, 184usize),
                    (1744830467u32, 143usize),
                    (1744830467u32, 256usize),
                    (268435454u32, 189usize),
                    (133099247u32, 144usize),
                    (1744830467u32, 257usize),
                    (268435454u32, 190usize),
                    (1744830467u32, 144usize),
                    (1744830467u32, 256usize),
                    (268435454u32, 195usize),
                    (133099247u32, 145usize),
                    (1744830467u32, 257usize),
                    (268435454u32, 196usize),
                    (1744830467u32, 145usize),
                    (1744830467u32, 256usize),
                    (268435454u32, 201usize),
                    (133099247u32, 146usize),
                    (1744830467u32, 257usize),
                    (268435454u32, 202usize),
                    (1744830467u32, 146usize),
                    (1744830467u32, 256usize),
                    (268435454u32, 207usize),
                    (133099247u32, 147usize),
                    (1744830467u32, 257usize),
                    (268435454u32, 208usize),
                    (1744830467u32, 147usize),
                    (1744830467u32, 256usize),
                    (268435454u32, 213usize),
                    (133099247u32, 148usize),
                    (1744830467u32, 257usize),
                    (268435454u32, 214usize),
                    (1744830467u32, 148usize),
                    (1744830467u32, 256usize),
                    (268435454u32, 217usize),
                    (133099247u32, 149usize),
                    (1744830467u32, 257usize),
                    (268435454u32, 218usize),
                    (1744830467u32, 149usize),
                    (1744830467u32, 256usize),
                    (268435454u32, 221usize),
                    (133099247u32, 150usize),
                    (1744830467u32, 257usize),
                    (268435454u32, 222usize),
                    (1744830467u32, 150usize),
                    (1744830467u32, 256usize),
                    (268435454u32, 225usize),
                    (133099247u32, 151usize),
                    (1744830467u32, 257usize),
                    (268435454u32, 226usize),
                    (1744830467u32, 151usize),
                    (1744830467u32, 256usize),
                    (268435454u32, 229usize),
                    (133099247u32, 152usize),
                    (1744830467u32, 257usize),
                    (268435454u32, 230usize),
                    (1744830467u32, 152usize),
                    (1744830467u32, 256usize),
                    (268435454u32, 233usize),
                    (133099247u32, 153usize),
                    (1744830467u32, 257usize),
                    (268435454u32, 234usize),
                    (1744830467u32, 153usize),
                    (1744830467u32, 256usize),
                    (268435454u32, 237usize),
                    (133099247u32, 154usize),
                    (1744830467u32, 257usize),
                    (268435454u32, 238usize),
                    (1744830467u32, 154usize),
                    (1744830467u32, 256usize),
                    (268435454u32, 241usize),
                    (133099247u32, 155usize),
                    (1744830467u32, 257usize),
                    (268435454u32, 242usize),
                    (1744830467u32, 155usize),
                    (1744830467u32, 256usize),
                    (268435454u32, 245usize),
                    (133099247u32, 156usize),
                    (1744830467u32, 257usize),
                    (268435454u32, 246usize),
                    (1744830467u32, 156usize),
                    (1744830467u32, 256usize),
                    (268435454u32, 249usize),
                    (133099247u32, 157usize),
                    (1744830467u32, 257usize),
                    (268435454u32, 250usize),
                    (1744830467u32, 157usize),
                ];
                let mut _sc = 0;
                while _sc < 38usize {
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
                const VL_DESCS: [(usize, usize, usize); 61usize] = [
                    (341usize, 0usize, 3usize),
                    (343usize, 3usize, 3usize),
                    (344usize, 6usize, 3usize),
                    (345usize, 9usize, 3usize),
                    (346usize, 12usize, 3usize),
                    (347usize, 15usize, 3usize),
                    (348usize, 18usize, 3usize),
                    (349usize, 21usize, 3usize),
                    (350usize, 24usize, 3usize),
                    (351usize, 27usize, 3usize),
                    (352usize, 30usize, 3usize),
                    (353usize, 33usize, 3usize),
                    (354usize, 36usize, 3usize),
                    (355usize, 39usize, 3usize),
                    (356usize, 42usize, 3usize),
                    (357usize, 45usize, 3usize),
                    (358usize, 48usize, 3usize),
                    (359usize, 51usize, 3usize),
                    (360usize, 54usize, 3usize),
                    (361usize, 57usize, 3usize),
                    (362usize, 60usize, 3usize),
                    (363usize, 63usize, 3usize),
                    (364usize, 66usize, 3usize),
                    (365usize, 69usize, 3usize),
                    (366usize, 72usize, 3usize),
                    (367usize, 75usize, 3usize),
                    (368usize, 78usize, 3usize),
                    (369usize, 81usize, 3usize),
                    (370usize, 84usize, 3usize),
                    (371usize, 87usize, 3usize),
                    (372usize, 90usize, 3usize),
                    (373usize, 93usize, 3usize),
                    (374usize, 96usize, 3usize),
                    (375usize, 99usize, 3usize),
                    (376usize, 102usize, 3usize),
                    (377usize, 105usize, 3usize),
                    (378usize, 108usize, 3usize),
                    (379usize, 111usize, 3usize),
                    (380usize, 114usize, 3usize),
                    (381usize, 117usize, 3usize),
                    (382usize, 120usize, 3usize),
                    (383usize, 123usize, 3usize),
                    (384usize, 126usize, 3usize),
                    (385usize, 129usize, 3usize),
                    (386usize, 132usize, 3usize),
                    (387usize, 135usize, 3usize),
                    (388usize, 138usize, 3usize),
                    (389usize, 141usize, 3usize),
                    (390usize, 144usize, 3usize),
                    (391usize, 147usize, 3usize),
                    (392usize, 150usize, 3usize),
                    (393usize, 153usize, 3usize),
                    (394usize, 156usize, 3usize),
                    (395usize, 159usize, 3usize),
                    (396usize, 162usize, 3usize),
                    (397usize, 165usize, 3usize),
                    (398usize, 168usize, 3usize),
                    (399usize, 171usize, 3usize),
                    (400usize, 174usize, 3usize),
                    (401usize, 177usize, 3usize),
                    (402usize, 180usize, 3usize),
                ];
                const VL_COLS: [(u32, usize, usize); 183usize] = [
                    (0u32, 0usize, 1usize),
                    (0u32, 1usize, 1usize),
                    (939524009u32, 2usize, 0usize),
                    (0u32, 2usize, 1usize),
                    (0u32, 3usize, 1usize),
                    (939524009u32, 4usize, 0usize),
                    (0u32, 4usize, 1usize),
                    (0u32, 5usize, 1usize),
                    (939524009u32, 6usize, 0usize),
                    (0u32, 6usize, 1usize),
                    (0u32, 7usize, 1usize),
                    (939524009u32, 8usize, 0usize),
                    (0u32, 8usize, 1usize),
                    (0u32, 9usize, 1usize),
                    (939524009u32, 10usize, 0usize),
                    (0u32, 10usize, 1usize),
                    (0u32, 11usize, 1usize),
                    (939524009u32, 12usize, 0usize),
                    (0u32, 12usize, 1usize),
                    (0u32, 13usize, 1usize),
                    (939524009u32, 14usize, 0usize),
                    (0u32, 14usize, 1usize),
                    (0u32, 15usize, 1usize),
                    (939524009u32, 16usize, 0usize),
                    (0u32, 16usize, 1usize),
                    (0u32, 17usize, 1usize),
                    (939524009u32, 18usize, 0usize),
                    (0u32, 18usize, 1usize),
                    (0u32, 19usize, 1usize),
                    (939524009u32, 20usize, 0usize),
                    (0u32, 20usize, 1usize),
                    (0u32, 21usize, 1usize),
                    (939524009u32, 22usize, 0usize),
                    (0u32, 22usize, 1usize),
                    (0u32, 23usize, 1usize),
                    (939524009u32, 24usize, 0usize),
                    (0u32, 24usize, 1usize),
                    (0u32, 25usize, 1usize),
                    (939524009u32, 26usize, 0usize),
                    (0u32, 26usize, 1usize),
                    (0u32, 27usize, 1usize),
                    (939524009u32, 28usize, 0usize),
                    (0u32, 28usize, 1usize),
                    (0u32, 29usize, 1usize),
                    (939524009u32, 30usize, 0usize),
                    (0u32, 30usize, 1usize),
                    (0u32, 31usize, 1usize),
                    (939524009u32, 32usize, 0usize),
                    (0u32, 32usize, 1usize),
                    (0u32, 33usize, 1usize),
                    (939524009u32, 34usize, 0usize),
                    (0u32, 34usize, 1usize),
                    (0u32, 35usize, 1usize),
                    (939524009u32, 36usize, 0usize),
                    (0u32, 36usize, 1usize),
                    (0u32, 37usize, 1usize),
                    (939524009u32, 38usize, 0usize),
                    (0u32, 38usize, 1usize),
                    (0u32, 39usize, 1usize),
                    (939524009u32, 40usize, 0usize),
                    (0u32, 40usize, 1usize),
                    (0u32, 41usize, 1usize),
                    (939524009u32, 42usize, 0usize),
                    (0u32, 42usize, 1usize),
                    (0u32, 43usize, 1usize),
                    (939524009u32, 44usize, 0usize),
                    (0u32, 44usize, 1usize),
                    (0u32, 45usize, 1usize),
                    (939524009u32, 46usize, 0usize),
                    (0u32, 46usize, 1usize),
                    (0u32, 47usize, 1usize),
                    (939524009u32, 48usize, 0usize),
                    (0u32, 48usize, 1usize),
                    (0u32, 49usize, 1usize),
                    (939524009u32, 50usize, 0usize),
                    (0u32, 50usize, 1usize),
                    (0u32, 51usize, 1usize),
                    (939524009u32, 52usize, 0usize),
                    (0u32, 52usize, 1usize),
                    (0u32, 53usize, 1usize),
                    (939524009u32, 54usize, 0usize),
                    (0u32, 54usize, 1usize),
                    (0u32, 55usize, 1usize),
                    (939524009u32, 56usize, 0usize),
                    (0u32, 56usize, 1usize),
                    (0u32, 57usize, 1usize),
                    (939524009u32, 58usize, 0usize),
                    (0u32, 58usize, 1usize),
                    (0u32, 59usize, 1usize),
                    (939524009u32, 60usize, 0usize),
                    (0u32, 60usize, 1usize),
                    (0u32, 61usize, 1usize),
                    (939524009u32, 62usize, 0usize),
                    (0u32, 62usize, 1usize),
                    (0u32, 63usize, 1usize),
                    (939524009u32, 64usize, 0usize),
                    (0u32, 64usize, 2usize),
                    (0u32, 66usize, 2usize),
                    (1879048146u32, 68usize, 0usize),
                    (0u32, 68usize, 2usize),
                    (0u32, 70usize, 2usize),
                    (134217679u32, 72usize, 0usize),
                    (0u32, 72usize, 2usize),
                    (0u32, 74usize, 0usize),
                    (402653133u32, 74usize, 0usize),
                    (0u32, 74usize, 2usize),
                    (0u32, 76usize, 0usize),
                    (402653133u32, 76usize, 0usize),
                    (0u32, 76usize, 2usize),
                    (0u32, 78usize, 0usize),
                    (402653133u32, 78usize, 0usize),
                    (0u32, 78usize, 2usize),
                    (0u32, 80usize, 0usize),
                    (402653133u32, 80usize, 0usize),
                    (0u32, 80usize, 2usize),
                    (0u32, 82usize, 0usize),
                    (671088587u32, 82usize, 0usize),
                    (0u32, 82usize, 2usize),
                    (0u32, 84usize, 0usize),
                    (671088587u32, 84usize, 0usize),
                    (0u32, 84usize, 2usize),
                    (0u32, 86usize, 0usize),
                    (671088587u32, 86usize, 0usize),
                    (0u32, 86usize, 2usize),
                    (0u32, 88usize, 0usize),
                    (671088587u32, 88usize, 0usize),
                    (0u32, 88usize, 2usize),
                    (0u32, 90usize, 0usize),
                    (671088587u32, 90usize, 0usize),
                    (0u32, 90usize, 2usize),
                    (0u32, 92usize, 0usize),
                    (671088587u32, 92usize, 0usize),
                    (0u32, 92usize, 2usize),
                    (0u32, 94usize, 0usize),
                    (671088587u32, 94usize, 0usize),
                    (0u32, 94usize, 2usize),
                    (0u32, 96usize, 0usize),
                    (671088587u32, 96usize, 0usize),
                    (0u32, 96usize, 2usize),
                    (0u32, 98usize, 0usize),
                    (939524041u32, 98usize, 0usize),
                    (0u32, 98usize, 2usize),
                    (0u32, 100usize, 0usize),
                    (939524041u32, 100usize, 0usize),
                    (0u32, 100usize, 2usize),
                    (0u32, 102usize, 0usize),
                    (939524041u32, 102usize, 0usize),
                    (0u32, 102usize, 2usize),
                    (0u32, 104usize, 0usize),
                    (939524041u32, 104usize, 0usize),
                    (0u32, 104usize, 2usize),
                    (0u32, 106usize, 0usize),
                    (939524041u32, 106usize, 0usize),
                    (0u32, 106usize, 2usize),
                    (0u32, 108usize, 0usize),
                    (939524041u32, 108usize, 0usize),
                    (0u32, 108usize, 2usize),
                    (0u32, 110usize, 0usize),
                    (939524041u32, 110usize, 0usize),
                    (0u32, 110usize, 2usize),
                    (0u32, 112usize, 0usize),
                    (939524041u32, 112usize, 0usize),
                    (0u32, 112usize, 2usize),
                    (0u32, 114usize, 0usize),
                    (939524041u32, 114usize, 0usize),
                    (0u32, 114usize, 2usize),
                    (0u32, 116usize, 0usize),
                    (939524041u32, 116usize, 0usize),
                    (0u32, 116usize, 2usize),
                    (0u32, 118usize, 0usize),
                    (939524041u32, 118usize, 0usize),
                    (0u32, 118usize, 2usize),
                    (0u32, 120usize, 0usize),
                    (939524041u32, 120usize, 0usize),
                    (0u32, 120usize, 2usize),
                    (0u32, 122usize, 0usize),
                    (939524041u32, 122usize, 0usize),
                    (0u32, 122usize, 2usize),
                    (0u32, 124usize, 0usize),
                    (939524041u32, 124usize, 0usize),
                    (0u32, 124usize, 2usize),
                    (0u32, 126usize, 0usize),
                    (939524041u32, 126usize, 0usize),
                ];
                const VL_TERMS: [(u32, usize); 126usize] = [
                    (268435454u32, 167usize),
                    (268435454u32, 40usize),
                    (268435454u32, 168usize),
                    (268435454u32, 41usize),
                    (268435454u32, 173usize),
                    (268435454u32, 42usize),
                    (268435454u32, 174usize),
                    (268435454u32, 43usize),
                    (268435454u32, 179usize),
                    (268435454u32, 44usize),
                    (268435454u32, 180usize),
                    (268435454u32, 45usize),
                    (268435454u32, 185usize),
                    (268435454u32, 46usize),
                    (268435454u32, 186usize),
                    (268435454u32, 47usize),
                    (268435454u32, 191usize),
                    (268435454u32, 48usize),
                    (268435454u32, 192usize),
                    (268435454u32, 49usize),
                    (268435454u32, 197usize),
                    (268435454u32, 50usize),
                    (268435454u32, 198usize),
                    (268435454u32, 51usize),
                    (268435454u32, 203usize),
                    (268435454u32, 52usize),
                    (268435454u32, 204usize),
                    (268435454u32, 53usize),
                    (268435454u32, 209usize),
                    (268435454u32, 54usize),
                    (268435454u32, 210usize),
                    (268435454u32, 55usize),
                    (268435454u32, 219usize),
                    (268435454u32, 56usize),
                    (268435454u32, 220usize),
                    (268435454u32, 57usize),
                    (268435454u32, 223usize),
                    (268435454u32, 58usize),
                    (268435454u32, 224usize),
                    (268435454u32, 59usize),
                    (268435454u32, 227usize),
                    (268435454u32, 60usize),
                    (268435454u32, 228usize),
                    (268435454u32, 61usize),
                    (268435454u32, 231usize),
                    (268435454u32, 62usize),
                    (268435454u32, 232usize),
                    (268435454u32, 63usize),
                    (268435454u32, 235usize),
                    (268435454u32, 64usize),
                    (268435454u32, 236usize),
                    (268435454u32, 65usize),
                    (268435454u32, 239usize),
                    (268435454u32, 66usize),
                    (268435454u32, 240usize),
                    (268435454u32, 67usize),
                    (268435454u32, 243usize),
                    (268435454u32, 68usize),
                    (268435454u32, 244usize),
                    (268435454u32, 69usize),
                    (268435454u32, 247usize),
                    (268435454u32, 70usize),
                    (268435454u32, 248usize),
                    (268435454u32, 71usize),
                    (2013200385u32, 72usize),
                    (65536u32, 104usize),
                    (2013200385u32, 102usize),
                    (65536u32, 134usize),
                    (2013200385u32, 73usize),
                    (65536u32, 105usize),
                    (2013200385u32, 101usize),
                    (65536u32, 133usize),
                    (2013200385u32, 74usize),
                    (65536u32, 106usize),
                    (2013200385u32, 75usize),
                    (65536u32, 107usize),
                    (2013200385u32, 99usize),
                    (65536u32, 131usize),
                    (2013200385u32, 100usize),
                    (65536u32, 132usize),
                    (2013200385u32, 76usize),
                    (65536u32, 108usize),
                    (2013200385u32, 77usize),
                    (65536u32, 109usize),
                    (2013200385u32, 78usize),
                    (65536u32, 110usize),
                    (2013200385u32, 79usize),
                    (65536u32, 111usize),
                    (2013200385u32, 95usize),
                    (65536u32, 127usize),
                    (2013200385u32, 96usize),
                    (65536u32, 128usize),
                    (2013200385u32, 97usize),
                    (65536u32, 129usize),
                    (2013200385u32, 98usize),
                    (65536u32, 130usize),
                    (2013200385u32, 80usize),
                    (65536u32, 112usize),
                    (2013200385u32, 81usize),
                    (65536u32, 113usize),
                    (2013200385u32, 82usize),
                    (65536u32, 114usize),
                    (2013200385u32, 83usize),
                    (65536u32, 115usize),
                    (2013200385u32, 84usize),
                    (65536u32, 116usize),
                    (2013200385u32, 85usize),
                    (65536u32, 117usize),
                    (2013200385u32, 86usize),
                    (65536u32, 118usize),
                    (2013200385u32, 87usize),
                    (65536u32, 119usize),
                    (2013200385u32, 88usize),
                    (65536u32, 120usize),
                    (2013200385u32, 89usize),
                    (65536u32, 121usize),
                    (2013200385u32, 90usize),
                    (65536u32, 122usize),
                    (2013200385u32, 91usize),
                    (65536u32, 123usize),
                    (2013200385u32, 92usize),
                    (65536u32, 124usize),
                    (2013200385u32, 93usize),
                    (65536u32, 125usize),
                    (2013200385u32, 94usize),
                    (65536u32, 126usize),
                ];
                let mut _vl = 0;
                while _vl < 61usize {
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
                const VS_DESCS: [(usize, usize, usize); 1usize] = [(342usize, 0usize, 3usize)];
                const VS_DEPS: [usize; 3usize] = [260usize, 261usize, 262usize];
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
