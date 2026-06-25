use super::common::{
    dot_eq, draw_field_els_into, draw_field_els_into_after_pow, draw_single_field_el,
    draw_single_field_el_after_pow, ext_from_nds, ext_from_raw_words, fold_standard_claims,
    make_eq_poly, read_field_el, read_reduced_field_el, verify_final_step_check,
    verify_sumcheck_rounds, EXT_DEGREE,
};
use super::constants::*;
use verifier_common::blake2s_u32::{BLAKE2S_BLOCK_SIZE_U32_WORDS, BLAKE2S_DIGEST_SIZE_U32_WORDS};
use verifier_common::errors::ErrorCreator;
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::field::{Field, FieldExtension, PrimeField};
use verifier_common::field_ops;
use verifier_common::gkr::SimpleGateType;
use verifier_common::gkr::{GKRVerifierOutput, LayerState};
use verifier_common::lazy_vec::LazyVec;
use verifier_common::non_determinism_source::NonDeterminismSource;
use verifier_common::structs::{CommitBuf, TranscriptState};
use verifier_common::whir::read_and_verify_pow;
use verifier_common::GKRExternalChallenges;
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_0_compute_claim(
    output_claims: &[BabyBearExt4; 160usize],
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
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_0_final_step_accumulator(
    evals: &[[BabyBearExt4; 1]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    lookup_alpha: BabyBearExt4,
    linearization_challenges: &[BabyBearExt4],
    permutation_argument_additive_part: BabyBearExt4,
    address_high_bits_shift: u32,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 21usize] = [
            (SimpleGateType::Copy, [212usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::Product,
                [217usize, 218usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [219usize, 220usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [221usize, 222usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [223usize, 224usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [225usize, 226usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [227usize, 228usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [229usize, 230usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [231usize, 232usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [233usize, 234usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [235usize, 236usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [237usize, 238usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [239usize, 240usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [241usize, 242usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [243usize, 244usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [245usize, 246usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [247usize, 248usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [249usize, 250usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [251usize, 252usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [253usize, 254usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [255usize, 256usize, 0usize, 0usize],
            ),
        ];
        let mut _sg = 0;
        while _sg < 21usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                SimpleGateType::Copy => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::Product => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::MaskToIdentity => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::UnbalancedProduct => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::LookupInitialPair => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupWithSetup => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupUnbalanced => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupAggregatePair => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupInitialWithCachedDenominators => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
            }
            _sg += 1;
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 63usize] = [
            (SimpleGateType::Copy, [135usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [136usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupWithSetup,
                [88usize, 158usize, 215usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [89usize, 90usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [91usize, 92usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [93usize, 94usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [95usize, 96usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [97usize, 98usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [99usize, 100usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [101usize, 102usize, 0usize, 0usize],
            ),
            (SimpleGateType::Copy, [103usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupWithSetup,
                [213usize, 159usize, 216usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [214usize, 257usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [258usize, 259usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [260usize, 261usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [262usize, 263usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [264usize, 265usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [266usize, 267usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [268usize, 269usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [270usize, 271usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [272usize, 273usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [274usize, 275usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [276usize, 277usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [278usize, 279usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [280usize, 281usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [282usize, 283usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [284usize, 285usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [286usize, 287usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [288usize, 289usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [290usize, 291usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [292usize, 293usize, 0usize, 0usize],
            ),
            (SimpleGateType::Copy, [294usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupWithSetup,
                [295usize, 160usize, 296usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [297usize, 298usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [299usize, 300usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [301usize, 302usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [303usize, 304usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [305usize, 306usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [307usize, 308usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [309usize, 310usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [311usize, 312usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [313usize, 314usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [315usize, 316usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [317usize, 318usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [319usize, 320usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [321usize, 322usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [323usize, 324usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [325usize, 326usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [327usize, 328usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [329usize, 330usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [331usize, 332usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [333usize, 334usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [335usize, 336usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [337usize, 338usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [339usize, 340usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [341usize, 342usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [343usize, 344usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [345usize, 346usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [347usize, 348usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [349usize, 350usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [351usize, 352usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [353usize, 354usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [355usize, 356usize, 0usize, 0usize],
            ),
        ];
        let mut _sg = 0;
        while _sg < 63usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                SimpleGateType::Copy => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::Product => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::MaskToIdentity => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::UnbalancedProduct => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::LookupInitialPair => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupWithSetup => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupUnbalanced => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupAggregatePair => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupInitialWithCachedDenominators => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
            }
            _sg += 1;
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(212usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(212usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(212usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (209usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (161usize, 268435454usize),
                (193usize, 268435454usize),
                (6usize, 268435454usize),
                (8usize, 268435454usize),
                (161usize, 1744830467usize),
                (193usize, 268435454usize),
                (6usize, 268435454usize),
                (8usize, 268435454usize),
                (161usize, 268435454usize),
                (193usize, 1744830467usize),
                (8usize, 268435454usize),
                (161usize, 1744830467usize),
                (193usize, 268435454usize),
                (7usize, 268435454usize),
                (8usize, 1744830467usize),
                (193usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(24usize, 1744970275usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (9usize, 1744830467usize),
                (162usize, 268435454usize),
                (194usize, 268435454usize),
                (9usize, 268435454usize),
                (162usize, 1744830467usize),
                (194usize, 268435454usize),
                (9usize, 268435454usize),
                (162usize, 268435454usize),
                (194usize, 1744830467usize),
                (9usize, 268435454usize),
                (162usize, 1744830467usize),
                (194usize, 268435454usize),
                (9usize, 1744830467usize),
                (194usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(24usize, 268435454usize), (25usize, 1744970275usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (10usize, 1744830467usize),
                (165usize, 268435454usize),
                (195usize, 268435454usize),
                (10usize, 268435454usize),
                (165usize, 1744830467usize),
                (195usize, 268435454usize),
                (10usize, 268435454usize),
                (165usize, 268435454usize),
                (195usize, 1744830467usize),
                (10usize, 268435454usize),
                (165usize, 1744830467usize),
                (195usize, 268435454usize),
                (10usize, 1744830467usize),
                (195usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(25usize, 268435454usize), (26usize, 1744970275usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (11usize, 1744830467usize),
                (166usize, 268435454usize),
                (196usize, 268435454usize),
                (11usize, 268435454usize),
                (166usize, 1744830467usize),
                (196usize, 268435454usize),
                (11usize, 268435454usize),
                (166usize, 268435454usize),
                (196usize, 1744830467usize),
                (11usize, 268435454usize),
                (166usize, 1744830467usize),
                (196usize, 268435454usize),
                (11usize, 1744830467usize),
                (196usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(26usize, 268435454usize), (27usize, 1744970275usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (12usize, 1744830467usize),
                (169usize, 268435454usize),
                (197usize, 268435454usize),
                (12usize, 268435454usize),
                (169usize, 1744830467usize),
                (197usize, 268435454usize),
                (12usize, 268435454usize),
                (169usize, 268435454usize),
                (197usize, 1744830467usize),
                (12usize, 268435454usize),
                (169usize, 1744830467usize),
                (197usize, 268435454usize),
                (12usize, 1744830467usize),
                (197usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(27usize, 268435454usize), (28usize, 1744970275usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (13usize, 1744830467usize),
                (170usize, 268435454usize),
                (198usize, 268435454usize),
                (13usize, 268435454usize),
                (170usize, 1744830467usize),
                (198usize, 268435454usize),
                (13usize, 268435454usize),
                (170usize, 268435454usize),
                (198usize, 1744830467usize),
                (13usize, 268435454usize),
                (170usize, 1744830467usize),
                (198usize, 268435454usize),
                (13usize, 1744830467usize),
                (198usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(28usize, 268435454usize), (29usize, 1744970275usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (14usize, 1744830467usize),
                (173usize, 268435454usize),
                (199usize, 268435454usize),
                (14usize, 268435454usize),
                (173usize, 1744830467usize),
                (199usize, 268435454usize),
                (14usize, 268435454usize),
                (173usize, 268435454usize),
                (199usize, 1744830467usize),
                (14usize, 268435454usize),
                (173usize, 1744830467usize),
                (199usize, 268435454usize),
                (14usize, 1744830467usize),
                (199usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(29usize, 268435454usize), (30usize, 1744970275usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (15usize, 1744830467usize),
                (174usize, 268435454usize),
                (200usize, 268435454usize),
                (15usize, 268435454usize),
                (174usize, 1744830467usize),
                (200usize, 268435454usize),
                (15usize, 268435454usize),
                (174usize, 268435454usize),
                (200usize, 1744830467usize),
                (15usize, 268435454usize),
                (174usize, 1744830467usize),
                (200usize, 268435454usize),
                (15usize, 1744830467usize),
                (200usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(30usize, 268435454usize), (31usize, 1744970275usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (16usize, 1744830467usize),
                (177usize, 268435454usize),
                (201usize, 268435454usize),
                (16usize, 268435454usize),
                (177usize, 1744830467usize),
                (201usize, 268435454usize),
                (16usize, 268435454usize),
                (177usize, 268435454usize),
                (201usize, 1744830467usize),
                (16usize, 268435454usize),
                (177usize, 1744830467usize),
                (201usize, 268435454usize),
                (16usize, 1744830467usize),
                (201usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(31usize, 268435454usize), (32usize, 1744970275usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (17usize, 1744830467usize),
                (178usize, 268435454usize),
                (202usize, 268435454usize),
                (17usize, 268435454usize),
                (178usize, 1744830467usize),
                (202usize, 268435454usize),
                (17usize, 268435454usize),
                (178usize, 268435454usize),
                (202usize, 1744830467usize),
                (17usize, 268435454usize),
                (178usize, 1744830467usize),
                (202usize, 268435454usize),
                (17usize, 1744830467usize),
                (202usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(32usize, 268435454usize), (33usize, 1744970275usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (18usize, 1744830467usize),
                (181usize, 268435454usize),
                (203usize, 268435454usize),
                (18usize, 268435454usize),
                (181usize, 1744830467usize),
                (203usize, 268435454usize),
                (18usize, 268435454usize),
                (181usize, 268435454usize),
                (203usize, 1744830467usize),
                (18usize, 268435454usize),
                (181usize, 1744830467usize),
                (203usize, 268435454usize),
                (18usize, 1744830467usize),
                (203usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(33usize, 268435454usize), (34usize, 1744970275usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (19usize, 1744830467usize),
                (182usize, 268435454usize),
                (204usize, 268435454usize),
                (19usize, 268435454usize),
                (182usize, 1744830467usize),
                (204usize, 268435454usize),
                (19usize, 268435454usize),
                (182usize, 268435454usize),
                (204usize, 1744830467usize),
                (19usize, 268435454usize),
                (182usize, 1744830467usize),
                (204usize, 268435454usize),
                (19usize, 1744830467usize),
                (204usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(34usize, 268435454usize), (35usize, 1744970275usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (20usize, 1744830467usize),
                (185usize, 268435454usize),
                (205usize, 268435454usize),
                (20usize, 268435454usize),
                (185usize, 1744830467usize),
                (205usize, 268435454usize),
                (20usize, 268435454usize),
                (185usize, 268435454usize),
                (205usize, 1744830467usize),
                (20usize, 268435454usize),
                (185usize, 1744830467usize),
                (205usize, 268435454usize),
                (20usize, 1744830467usize),
                (205usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(35usize, 268435454usize), (36usize, 1744970275usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (21usize, 1744830467usize),
                (186usize, 268435454usize),
                (206usize, 268435454usize),
                (21usize, 268435454usize),
                (186usize, 1744830467usize),
                (206usize, 268435454usize),
                (21usize, 268435454usize),
                (186usize, 268435454usize),
                (206usize, 1744830467usize),
                (21usize, 268435454usize),
                (186usize, 1744830467usize),
                (206usize, 268435454usize),
                (21usize, 1744830467usize),
                (206usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(36usize, 268435454usize), (37usize, 1744970275usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (22usize, 1744830467usize),
                (189usize, 268435454usize),
                (207usize, 268435454usize),
                (22usize, 268435454usize),
                (189usize, 1744830467usize),
                (207usize, 268435454usize),
                (22usize, 268435454usize),
                (189usize, 268435454usize),
                (207usize, 1744830467usize),
                (22usize, 268435454usize),
                (189usize, 1744830467usize),
                (207usize, 268435454usize),
                (22usize, 1744830467usize),
                (207usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(37usize, 268435454usize), (38usize, 1744970275usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (0usize, 3usize),
                (1usize, 3usize),
                (2usize, 3usize),
                (5usize, 3usize),
                (7usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 14usize] = [
                (23usize, 1744830467usize),
                (190usize, 268435454usize),
                (208usize, 268435454usize),
                (23usize, 268435454usize),
                (190usize, 1744830467usize),
                (208usize, 268435454usize),
                (23usize, 268435454usize),
                (190usize, 268435454usize),
                (208usize, 1744830467usize),
                (23usize, 268435454usize),
                (190usize, 1744830467usize),
                (208usize, 268435454usize),
                (23usize, 1744830467usize),
                (208usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(38usize, 268435454usize), (39usize, 1744970275usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 2usize] = [(40usize, 2usize), (56usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (56usize, 1744830467usize),
                (193usize, 268435454usize),
                (161usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(104usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (40usize, 4usize),
                (41usize, 2usize),
                (56usize, 2usize),
                (57usize, 1usize),
                (161usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 10usize] = [
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (193usize, 2013200385usize),
                (194usize, 268435454usize),
                (56usize, 1744830467usize),
                (193usize, 268435454usize),
                (161usize, 2013200385usize),
                (162usize, 268435454usize),
                (161usize, 268435454usize),
                (193usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (72usize, 2013200385usize),
                (104usize, 65536usize),
                (105usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 8usize] = [
                (40usize, 4usize),
                (41usize, 4usize),
                (42usize, 2usize),
                (56usize, 2usize),
                (57usize, 2usize),
                (58usize, 1usize),
                (161usize, 1usize),
                (162usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 17usize] = [
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (194usize, 2013200385usize),
                (195usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (193usize, 2013200385usize),
                (194usize, 268435454usize),
                (56usize, 1744830467usize),
                (193usize, 268435454usize),
                (162usize, 2013200385usize),
                (165usize, 268435454usize),
                (161usize, 2013200385usize),
                (162usize, 268435454usize),
                (161usize, 268435454usize),
                (194usize, 65536usize),
                (193usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (73usize, 2013200385usize),
                (105usize, 65536usize),
                (106usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 11usize] = [
                (40usize, 4usize),
                (41usize, 4usize),
                (42usize, 4usize),
                (43usize, 2usize),
                (56usize, 2usize),
                (57usize, 2usize),
                (58usize, 2usize),
                (59usize, 1usize),
                (161usize, 1usize),
                (162usize, 1usize),
                (165usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 24usize] = [
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (195usize, 2013200385usize),
                (196usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (194usize, 2013200385usize),
                (195usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (193usize, 2013200385usize),
                (194usize, 268435454usize),
                (56usize, 1744830467usize),
                (193usize, 268435454usize),
                (165usize, 2013200385usize),
                (166usize, 268435454usize),
                (162usize, 2013200385usize),
                (165usize, 268435454usize),
                (161usize, 2013200385usize),
                (162usize, 268435454usize),
                (161usize, 268435454usize),
                (195usize, 65536usize),
                (194usize, 65536usize),
                (193usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (74usize, 2013200385usize),
                (106usize, 65536usize),
                (107usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (161usize, 1usize),
                (162usize, 1usize),
                (165usize, 1usize),
                (166usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 31usize] = [
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (196usize, 2013200385usize),
                (197usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (195usize, 2013200385usize),
                (196usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (194usize, 2013200385usize),
                (195usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (193usize, 2013200385usize),
                (194usize, 268435454usize),
                (56usize, 1744830467usize),
                (193usize, 268435454usize),
                (166usize, 2013200385usize),
                (169usize, 268435454usize),
                (165usize, 2013200385usize),
                (166usize, 268435454usize),
                (162usize, 2013200385usize),
                (165usize, 268435454usize),
                (161usize, 2013200385usize),
                (162usize, 268435454usize),
                (161usize, 268435454usize),
                (196usize, 65536usize),
                (195usize, 65536usize),
                (194usize, 65536usize),
                (193usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (75usize, 2013200385usize),
                (107usize, 65536usize),
                (108usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (161usize, 1usize),
                (162usize, 1usize),
                (165usize, 1usize),
                (166usize, 1usize),
                (169usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 38usize] = [
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (196usize, 2013200385usize),
                (197usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (195usize, 2013200385usize),
                (196usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (194usize, 2013200385usize),
                (195usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (193usize, 2013200385usize),
                (194usize, 268435454usize),
                (56usize, 1744830467usize),
                (193usize, 268435454usize),
                (169usize, 2013200385usize),
                (170usize, 268435454usize),
                (166usize, 2013200385usize),
                (169usize, 268435454usize),
                (165usize, 2013200385usize),
                (166usize, 268435454usize),
                (162usize, 2013200385usize),
                (165usize, 268435454usize),
                (161usize, 2013200385usize),
                (162usize, 268435454usize),
                (161usize, 268435454usize),
                (197usize, 65536usize),
                (196usize, 65536usize),
                (195usize, 65536usize),
                (194usize, 65536usize),
                (193usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (76usize, 2013200385usize),
                (108usize, 65536usize),
                (109usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (161usize, 1usize),
                (162usize, 1usize),
                (165usize, 1usize),
                (166usize, 1usize),
                (169usize, 1usize),
                (170usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 45usize] = [
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (198usize, 2013200385usize),
                (199usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (196usize, 2013200385usize),
                (197usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (195usize, 2013200385usize),
                (196usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (194usize, 2013200385usize),
                (195usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (193usize, 2013200385usize),
                (194usize, 268435454usize),
                (56usize, 1744830467usize),
                (193usize, 268435454usize),
                (170usize, 2013200385usize),
                (173usize, 268435454usize),
                (169usize, 2013200385usize),
                (170usize, 268435454usize),
                (166usize, 2013200385usize),
                (169usize, 268435454usize),
                (165usize, 2013200385usize),
                (166usize, 268435454usize),
                (162usize, 2013200385usize),
                (165usize, 268435454usize),
                (161usize, 2013200385usize),
                (162usize, 268435454usize),
                (161usize, 268435454usize),
                (198usize, 65536usize),
                (197usize, 65536usize),
                (196usize, 65536usize),
                (195usize, 65536usize),
                (194usize, 65536usize),
                (193usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (77usize, 2013200385usize),
                (109usize, 65536usize),
                (110usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (161usize, 1usize),
                (162usize, 1usize),
                (165usize, 1usize),
                (166usize, 1usize),
                (169usize, 1usize),
                (170usize, 1usize),
                (173usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 52usize] = [
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (199usize, 2013200385usize),
                (200usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (198usize, 2013200385usize),
                (199usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (196usize, 2013200385usize),
                (197usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (195usize, 2013200385usize),
                (196usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (194usize, 2013200385usize),
                (195usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (193usize, 2013200385usize),
                (194usize, 268435454usize),
                (56usize, 1744830467usize),
                (193usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (170usize, 2013200385usize),
                (173usize, 268435454usize),
                (169usize, 2013200385usize),
                (170usize, 268435454usize),
                (166usize, 2013200385usize),
                (169usize, 268435454usize),
                (165usize, 2013200385usize),
                (166usize, 268435454usize),
                (162usize, 2013200385usize),
                (165usize, 268435454usize),
                (161usize, 2013200385usize),
                (162usize, 268435454usize),
                (161usize, 268435454usize),
                (199usize, 65536usize),
                (198usize, 65536usize),
                (197usize, 65536usize),
                (196usize, 65536usize),
                (195usize, 65536usize),
                (194usize, 65536usize),
                (193usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (78usize, 2013200385usize),
                (110usize, 65536usize),
                (111usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (161usize, 1usize),
                (162usize, 1usize),
                (165usize, 1usize),
                (166usize, 1usize),
                (169usize, 1usize),
                (170usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 59usize] = [
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (200usize, 2013200385usize),
                (201usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (199usize, 2013200385usize),
                (200usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (198usize, 2013200385usize),
                (199usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (196usize, 2013200385usize),
                (197usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (195usize, 2013200385usize),
                (196usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (194usize, 2013200385usize),
                (195usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (193usize, 2013200385usize),
                (194usize, 268435454usize),
                (56usize, 1744830467usize),
                (193usize, 268435454usize),
                (174usize, 2013200385usize),
                (177usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (170usize, 2013200385usize),
                (173usize, 268435454usize),
                (169usize, 2013200385usize),
                (170usize, 268435454usize),
                (166usize, 2013200385usize),
                (169usize, 268435454usize),
                (165usize, 2013200385usize),
                (166usize, 268435454usize),
                (162usize, 2013200385usize),
                (165usize, 268435454usize),
                (161usize, 2013200385usize),
                (162usize, 268435454usize),
                (161usize, 268435454usize),
                (200usize, 65536usize),
                (199usize, 65536usize),
                (198usize, 65536usize),
                (197usize, 65536usize),
                (196usize, 65536usize),
                (195usize, 65536usize),
                (194usize, 65536usize),
                (193usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (79usize, 2013200385usize),
                (111usize, 65536usize),
                (112usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (161usize, 1usize),
                (162usize, 1usize),
                (165usize, 1usize),
                (166usize, 1usize),
                (169usize, 1usize),
                (170usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (177usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 66usize] = [
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (201usize, 2013200385usize),
                (202usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (200usize, 2013200385usize),
                (201usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (199usize, 2013200385usize),
                (200usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (198usize, 2013200385usize),
                (199usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (196usize, 2013200385usize),
                (197usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (195usize, 2013200385usize),
                (196usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (194usize, 2013200385usize),
                (195usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (193usize, 2013200385usize),
                (194usize, 268435454usize),
                (56usize, 1744830467usize),
                (193usize, 268435454usize),
                (177usize, 2013200385usize),
                (178usize, 268435454usize),
                (174usize, 2013200385usize),
                (177usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (170usize, 2013200385usize),
                (173usize, 268435454usize),
                (169usize, 2013200385usize),
                (170usize, 268435454usize),
                (166usize, 2013200385usize),
                (169usize, 268435454usize),
                (165usize, 2013200385usize),
                (166usize, 268435454usize),
                (162usize, 2013200385usize),
                (165usize, 268435454usize),
                (161usize, 2013200385usize),
                (162usize, 268435454usize),
                (161usize, 268435454usize),
                (201usize, 65536usize),
                (200usize, 65536usize),
                (199usize, 65536usize),
                (198usize, 65536usize),
                (197usize, 65536usize),
                (196usize, 65536usize),
                (195usize, 65536usize),
                (194usize, 65536usize),
                (193usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (80usize, 2013200385usize),
                (112usize, 65536usize),
                (113usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (161usize, 1usize),
                (162usize, 1usize),
                (165usize, 1usize),
                (166usize, 1usize),
                (169usize, 1usize),
                (170usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (177usize, 1usize),
                (178usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 73usize] = [
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (202usize, 2013200385usize),
                (203usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (201usize, 2013200385usize),
                (202usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (200usize, 2013200385usize),
                (201usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (199usize, 2013200385usize),
                (200usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (198usize, 2013200385usize),
                (199usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (196usize, 2013200385usize),
                (197usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (195usize, 2013200385usize),
                (196usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (194usize, 2013200385usize),
                (195usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (193usize, 2013200385usize),
                (194usize, 268435454usize),
                (56usize, 1744830467usize),
                (193usize, 268435454usize),
                (178usize, 2013200385usize),
                (181usize, 268435454usize),
                (177usize, 2013200385usize),
                (178usize, 268435454usize),
                (174usize, 2013200385usize),
                (177usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (170usize, 2013200385usize),
                (173usize, 268435454usize),
                (169usize, 2013200385usize),
                (170usize, 268435454usize),
                (166usize, 2013200385usize),
                (169usize, 268435454usize),
                (165usize, 2013200385usize),
                (166usize, 268435454usize),
                (162usize, 2013200385usize),
                (165usize, 268435454usize),
                (161usize, 2013200385usize),
                (162usize, 268435454usize),
                (161usize, 268435454usize),
                (202usize, 65536usize),
                (201usize, 65536usize),
                (200usize, 65536usize),
                (199usize, 65536usize),
                (198usize, 65536usize),
                (197usize, 65536usize),
                (196usize, 65536usize),
                (195usize, 65536usize),
                (194usize, 65536usize),
                (193usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (81usize, 2013200385usize),
                (113usize, 65536usize),
                (114usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (161usize, 1usize),
                (162usize, 1usize),
                (165usize, 1usize),
                (166usize, 1usize),
                (169usize, 1usize),
                (170usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (177usize, 1usize),
                (178usize, 1usize),
                (181usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 80usize] = [
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (202usize, 2013200385usize),
                (203usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (201usize, 2013200385usize),
                (202usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (200usize, 2013200385usize),
                (201usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (199usize, 2013200385usize),
                (200usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (198usize, 2013200385usize),
                (199usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (196usize, 2013200385usize),
                (197usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (195usize, 2013200385usize),
                (196usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (194usize, 2013200385usize),
                (195usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (193usize, 2013200385usize),
                (194usize, 268435454usize),
                (56usize, 1744830467usize),
                (193usize, 268435454usize),
                (181usize, 2013200385usize),
                (182usize, 268435454usize),
                (178usize, 2013200385usize),
                (181usize, 268435454usize),
                (177usize, 2013200385usize),
                (178usize, 268435454usize),
                (174usize, 2013200385usize),
                (177usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (170usize, 2013200385usize),
                (173usize, 268435454usize),
                (169usize, 2013200385usize),
                (170usize, 268435454usize),
                (166usize, 2013200385usize),
                (169usize, 268435454usize),
                (165usize, 2013200385usize),
                (166usize, 268435454usize),
                (162usize, 2013200385usize),
                (165usize, 268435454usize),
                (161usize, 2013200385usize),
                (162usize, 268435454usize),
                (161usize, 268435454usize),
                (203usize, 65536usize),
                (202usize, 65536usize),
                (201usize, 65536usize),
                (200usize, 65536usize),
                (199usize, 65536usize),
                (198usize, 65536usize),
                (197usize, 65536usize),
                (196usize, 65536usize),
                (195usize, 65536usize),
                (194usize, 65536usize),
                (193usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (82usize, 2013200385usize),
                (114usize, 65536usize),
                (115usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (161usize, 1usize),
                (162usize, 1usize),
                (165usize, 1usize),
                (166usize, 1usize),
                (169usize, 1usize),
                (170usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (177usize, 1usize),
                (178usize, 1usize),
                (181usize, 1usize),
                (182usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 87usize] = [
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (204usize, 2013200385usize),
                (205usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (202usize, 2013200385usize),
                (203usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (201usize, 2013200385usize),
                (202usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (200usize, 2013200385usize),
                (201usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (199usize, 2013200385usize),
                (200usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (198usize, 2013200385usize),
                (199usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (196usize, 2013200385usize),
                (197usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (195usize, 2013200385usize),
                (196usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (194usize, 2013200385usize),
                (195usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (193usize, 2013200385usize),
                (194usize, 268435454usize),
                (56usize, 1744830467usize),
                (193usize, 268435454usize),
                (182usize, 2013200385usize),
                (185usize, 268435454usize),
                (181usize, 2013200385usize),
                (182usize, 268435454usize),
                (178usize, 2013200385usize),
                (181usize, 268435454usize),
                (177usize, 2013200385usize),
                (178usize, 268435454usize),
                (174usize, 2013200385usize),
                (177usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (170usize, 2013200385usize),
                (173usize, 268435454usize),
                (169usize, 2013200385usize),
                (170usize, 268435454usize),
                (166usize, 2013200385usize),
                (169usize, 268435454usize),
                (165usize, 2013200385usize),
                (166usize, 268435454usize),
                (162usize, 2013200385usize),
                (165usize, 268435454usize),
                (161usize, 2013200385usize),
                (162usize, 268435454usize),
                (161usize, 268435454usize),
                (204usize, 65536usize),
                (203usize, 65536usize),
                (202usize, 65536usize),
                (201usize, 65536usize),
                (200usize, 65536usize),
                (199usize, 65536usize),
                (198usize, 65536usize),
                (197usize, 65536usize),
                (196usize, 65536usize),
                (195usize, 65536usize),
                (194usize, 65536usize),
                (193usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (83usize, 2013200385usize),
                (115usize, 65536usize),
                (116usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (161usize, 1usize),
                (162usize, 1usize),
                (165usize, 1usize),
                (166usize, 1usize),
                (169usize, 1usize),
                (170usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (177usize, 1usize),
                (178usize, 1usize),
                (181usize, 1usize),
                (182usize, 1usize),
                (185usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 94usize] = [
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (205usize, 2013200385usize),
                (206usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (204usize, 2013200385usize),
                (205usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (202usize, 2013200385usize),
                (203usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (201usize, 2013200385usize),
                (202usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (200usize, 2013200385usize),
                (201usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (199usize, 2013200385usize),
                (200usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (198usize, 2013200385usize),
                (199usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (196usize, 2013200385usize),
                (197usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (195usize, 2013200385usize),
                (196usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (194usize, 2013200385usize),
                (195usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (193usize, 2013200385usize),
                (194usize, 268435454usize),
                (56usize, 1744830467usize),
                (193usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (182usize, 2013200385usize),
                (185usize, 268435454usize),
                (181usize, 2013200385usize),
                (182usize, 268435454usize),
                (178usize, 2013200385usize),
                (181usize, 268435454usize),
                (177usize, 2013200385usize),
                (178usize, 268435454usize),
                (174usize, 2013200385usize),
                (177usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (170usize, 2013200385usize),
                (173usize, 268435454usize),
                (169usize, 2013200385usize),
                (170usize, 268435454usize),
                (166usize, 2013200385usize),
                (169usize, 268435454usize),
                (165usize, 2013200385usize),
                (166usize, 268435454usize),
                (162usize, 2013200385usize),
                (165usize, 268435454usize),
                (161usize, 2013200385usize),
                (162usize, 268435454usize),
                (161usize, 268435454usize),
                (205usize, 65536usize),
                (204usize, 65536usize),
                (203usize, 65536usize),
                (202usize, 65536usize),
                (201usize, 65536usize),
                (200usize, 65536usize),
                (199usize, 65536usize),
                (198usize, 65536usize),
                (197usize, 65536usize),
                (196usize, 65536usize),
                (195usize, 65536usize),
                (194usize, 65536usize),
                (193usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (84usize, 2013200385usize),
                (116usize, 65536usize),
                (117usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (161usize, 1usize),
                (162usize, 1usize),
                (165usize, 1usize),
                (166usize, 1usize),
                (169usize, 1usize),
                (170usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (177usize, 1usize),
                (178usize, 1usize),
                (181usize, 1usize),
                (182usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 101usize] = [
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (206usize, 2013200385usize),
                (207usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (205usize, 2013200385usize),
                (206usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (204usize, 2013200385usize),
                (205usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (202usize, 2013200385usize),
                (203usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (201usize, 2013200385usize),
                (202usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (200usize, 2013200385usize),
                (201usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (199usize, 2013200385usize),
                (200usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (198usize, 2013200385usize),
                (199usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (196usize, 2013200385usize),
                (197usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (195usize, 2013200385usize),
                (196usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (194usize, 2013200385usize),
                (195usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (193usize, 2013200385usize),
                (194usize, 268435454usize),
                (56usize, 1744830467usize),
                (193usize, 268435454usize),
                (186usize, 2013200385usize),
                (189usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (182usize, 2013200385usize),
                (185usize, 268435454usize),
                (181usize, 2013200385usize),
                (182usize, 268435454usize),
                (178usize, 2013200385usize),
                (181usize, 268435454usize),
                (177usize, 2013200385usize),
                (178usize, 268435454usize),
                (174usize, 2013200385usize),
                (177usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (170usize, 2013200385usize),
                (173usize, 268435454usize),
                (169usize, 2013200385usize),
                (170usize, 268435454usize),
                (166usize, 2013200385usize),
                (169usize, 268435454usize),
                (165usize, 2013200385usize),
                (166usize, 268435454usize),
                (162usize, 2013200385usize),
                (165usize, 268435454usize),
                (161usize, 2013200385usize),
                (162usize, 268435454usize),
                (161usize, 268435454usize),
                (206usize, 65536usize),
                (205usize, 65536usize),
                (204usize, 65536usize),
                (203usize, 65536usize),
                (202usize, 65536usize),
                (201usize, 65536usize),
                (200usize, 65536usize),
                (199usize, 65536usize),
                (198usize, 65536usize),
                (197usize, 65536usize),
                (196usize, 65536usize),
                (195usize, 65536usize),
                (194usize, 65536usize),
                (193usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (85usize, 2013200385usize),
                (117usize, 65536usize),
                (118usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (161usize, 1usize),
                (162usize, 1usize),
                (165usize, 1usize),
                (166usize, 1usize),
                (169usize, 1usize),
                (170usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (177usize, 1usize),
                (178usize, 1usize),
                (181usize, 1usize),
                (182usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (189usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 108usize] = [
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (207usize, 2013200385usize),
                (208usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (206usize, 2013200385usize),
                (207usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (205usize, 2013200385usize),
                (206usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (204usize, 2013200385usize),
                (205usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (202usize, 2013200385usize),
                (203usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (201usize, 2013200385usize),
                (202usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (200usize, 2013200385usize),
                (201usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (199usize, 2013200385usize),
                (200usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (198usize, 2013200385usize),
                (199usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (196usize, 2013200385usize),
                (197usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (195usize, 2013200385usize),
                (196usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (194usize, 2013200385usize),
                (195usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (193usize, 2013200385usize),
                (194usize, 268435454usize),
                (56usize, 1744830467usize),
                (193usize, 268435454usize),
                (189usize, 2013200385usize),
                (190usize, 268435454usize),
                (186usize, 2013200385usize),
                (189usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (182usize, 2013200385usize),
                (185usize, 268435454usize),
                (181usize, 2013200385usize),
                (182usize, 268435454usize),
                (178usize, 2013200385usize),
                (181usize, 268435454usize),
                (177usize, 2013200385usize),
                (178usize, 268435454usize),
                (174usize, 2013200385usize),
                (177usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (170usize, 2013200385usize),
                (173usize, 268435454usize),
                (169usize, 2013200385usize),
                (170usize, 268435454usize),
                (166usize, 2013200385usize),
                (169usize, 268435454usize),
                (165usize, 2013200385usize),
                (166usize, 268435454usize),
                (162usize, 2013200385usize),
                (165usize, 268435454usize),
                (161usize, 2013200385usize),
                (162usize, 268435454usize),
                (161usize, 268435454usize),
                (207usize, 65536usize),
                (206usize, 65536usize),
                (205usize, 65536usize),
                (204usize, 65536usize),
                (203usize, 65536usize),
                (202usize, 65536usize),
                (201usize, 65536usize),
                (200usize, 65536usize),
                (199usize, 65536usize),
                (198usize, 65536usize),
                (197usize, 65536usize),
                (196usize, 65536usize),
                (195usize, 65536usize),
                (194usize, 65536usize),
                (193usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (86usize, 2013200385usize),
                (118usize, 65536usize),
                (119usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (161usize, 1usize),
                (162usize, 1usize),
                (165usize, 1usize),
                (166usize, 1usize),
                (169usize, 1usize),
                (170usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (177usize, 1usize),
                (178usize, 1usize),
                (181usize, 1usize),
                (182usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (189usize, 1usize),
                (190usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 109usize] = [
                (71usize, 65536usize),
                (208usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (207usize, 2013200385usize),
                (208usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (206usize, 2013200385usize),
                (207usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (205usize, 2013200385usize),
                (206usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (204usize, 2013200385usize),
                (205usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (202usize, 2013200385usize),
                (203usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (201usize, 2013200385usize),
                (202usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (200usize, 2013200385usize),
                (201usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (199usize, 2013200385usize),
                (200usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (198usize, 2013200385usize),
                (199usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (196usize, 2013200385usize),
                (197usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (195usize, 2013200385usize),
                (196usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (194usize, 2013200385usize),
                (195usize, 268435454usize),
                (56usize, 65536usize),
                (57usize, 1744830467usize),
                (193usize, 2013200385usize),
                (194usize, 268435454usize),
                (190usize, 2013200385usize),
                (189usize, 2013200385usize),
                (190usize, 268435454usize),
                (186usize, 2013200385usize),
                (189usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (182usize, 2013200385usize),
                (185usize, 268435454usize),
                (181usize, 2013200385usize),
                (182usize, 268435454usize),
                (178usize, 2013200385usize),
                (181usize, 268435454usize),
                (177usize, 2013200385usize),
                (178usize, 268435454usize),
                (174usize, 2013200385usize),
                (177usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (170usize, 2013200385usize),
                (173usize, 268435454usize),
                (169usize, 2013200385usize),
                (170usize, 268435454usize),
                (166usize, 2013200385usize),
                (169usize, 268435454usize),
                (165usize, 2013200385usize),
                (166usize, 268435454usize),
                (162usize, 2013200385usize),
                (165usize, 268435454usize),
                (161usize, 2013200385usize),
                (162usize, 268435454usize),
                (208usize, 65536usize),
                (207usize, 65536usize),
                (206usize, 65536usize),
                (205usize, 65536usize),
                (204usize, 65536usize),
                (203usize, 65536usize),
                (202usize, 65536usize),
                (201usize, 65536usize),
                (200usize, 65536usize),
                (199usize, 65536usize),
                (198usize, 65536usize),
                (197usize, 65536usize),
                (196usize, 65536usize),
                (195usize, 65536usize),
                (194usize, 65536usize),
                (193usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (87usize, 2013200385usize),
                (119usize, 65536usize),
                (120usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (162usize, 1usize),
                (165usize, 1usize),
                (166usize, 1usize),
                (169usize, 1usize),
                (170usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (177usize, 1usize),
                (178usize, 1usize),
                (181usize, 1usize),
                (182usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (189usize, 1usize),
                (190usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 102usize] = [
                (71usize, 65536usize),
                (208usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (207usize, 2013200385usize),
                (208usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (206usize, 2013200385usize),
                (207usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (205usize, 2013200385usize),
                (206usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (204usize, 2013200385usize),
                (205usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (202usize, 2013200385usize),
                (203usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (201usize, 2013200385usize),
                (202usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (200usize, 2013200385usize),
                (201usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (199usize, 2013200385usize),
                (200usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (198usize, 2013200385usize),
                (199usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (196usize, 2013200385usize),
                (197usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (195usize, 2013200385usize),
                (196usize, 268435454usize),
                (57usize, 65536usize),
                (58usize, 1744830467usize),
                (194usize, 2013200385usize),
                (195usize, 268435454usize),
                (190usize, 2013200385usize),
                (189usize, 2013200385usize),
                (190usize, 268435454usize),
                (186usize, 2013200385usize),
                (189usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (182usize, 2013200385usize),
                (185usize, 268435454usize),
                (181usize, 2013200385usize),
                (182usize, 268435454usize),
                (178usize, 2013200385usize),
                (181usize, 268435454usize),
                (177usize, 2013200385usize),
                (178usize, 268435454usize),
                (174usize, 2013200385usize),
                (177usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (170usize, 2013200385usize),
                (173usize, 268435454usize),
                (169usize, 2013200385usize),
                (170usize, 268435454usize),
                (166usize, 2013200385usize),
                (169usize, 268435454usize),
                (165usize, 2013200385usize),
                (166usize, 268435454usize),
                (162usize, 2013200385usize),
                (165usize, 268435454usize),
                (208usize, 65536usize),
                (207usize, 65536usize),
                (206usize, 65536usize),
                (205usize, 65536usize),
                (204usize, 65536usize),
                (203usize, 65536usize),
                (202usize, 65536usize),
                (201usize, 65536usize),
                (200usize, 65536usize),
                (199usize, 65536usize),
                (198usize, 65536usize),
                (197usize, 65536usize),
                (196usize, 65536usize),
                (195usize, 65536usize),
                (194usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (88usize, 2013200385usize),
                (120usize, 65536usize),
                (121usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (165usize, 1usize),
                (166usize, 1usize),
                (169usize, 1usize),
                (170usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (177usize, 1usize),
                (178usize, 1usize),
                (181usize, 1usize),
                (182usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (189usize, 1usize),
                (190usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 95usize] = [
                (71usize, 65536usize),
                (208usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (207usize, 2013200385usize),
                (208usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (206usize, 2013200385usize),
                (207usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (205usize, 2013200385usize),
                (206usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (204usize, 2013200385usize),
                (205usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (202usize, 2013200385usize),
                (203usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (201usize, 2013200385usize),
                (202usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (200usize, 2013200385usize),
                (201usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (199usize, 2013200385usize),
                (200usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (198usize, 2013200385usize),
                (199usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (196usize, 2013200385usize),
                (197usize, 268435454usize),
                (58usize, 65536usize),
                (59usize, 1744830467usize),
                (195usize, 2013200385usize),
                (196usize, 268435454usize),
                (190usize, 2013200385usize),
                (189usize, 2013200385usize),
                (190usize, 268435454usize),
                (186usize, 2013200385usize),
                (189usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (182usize, 2013200385usize),
                (185usize, 268435454usize),
                (181usize, 2013200385usize),
                (182usize, 268435454usize),
                (178usize, 2013200385usize),
                (181usize, 268435454usize),
                (177usize, 2013200385usize),
                (178usize, 268435454usize),
                (174usize, 2013200385usize),
                (177usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (170usize, 2013200385usize),
                (173usize, 268435454usize),
                (169usize, 2013200385usize),
                (170usize, 268435454usize),
                (166usize, 2013200385usize),
                (169usize, 268435454usize),
                (165usize, 2013200385usize),
                (166usize, 268435454usize),
                (208usize, 65536usize),
                (207usize, 65536usize),
                (206usize, 65536usize),
                (205usize, 65536usize),
                (204usize, 65536usize),
                (203usize, 65536usize),
                (202usize, 65536usize),
                (201usize, 65536usize),
                (200usize, 65536usize),
                (199usize, 65536usize),
                (198usize, 65536usize),
                (197usize, 65536usize),
                (196usize, 65536usize),
                (195usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (89usize, 2013200385usize),
                (121usize, 65536usize),
                (122usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (166usize, 1usize),
                (169usize, 1usize),
                (170usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (177usize, 1usize),
                (178usize, 1usize),
                (181usize, 1usize),
                (182usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (189usize, 1usize),
                (190usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 88usize] = [
                (71usize, 65536usize),
                (208usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (207usize, 2013200385usize),
                (208usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (206usize, 2013200385usize),
                (207usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (205usize, 2013200385usize),
                (206usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (204usize, 2013200385usize),
                (205usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (202usize, 2013200385usize),
                (203usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (201usize, 2013200385usize),
                (202usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (200usize, 2013200385usize),
                (201usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (199usize, 2013200385usize),
                (200usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (198usize, 2013200385usize),
                (199usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (59usize, 65536usize),
                (60usize, 1744830467usize),
                (196usize, 2013200385usize),
                (197usize, 268435454usize),
                (190usize, 2013200385usize),
                (189usize, 2013200385usize),
                (190usize, 268435454usize),
                (186usize, 2013200385usize),
                (189usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (182usize, 2013200385usize),
                (185usize, 268435454usize),
                (181usize, 2013200385usize),
                (182usize, 268435454usize),
                (178usize, 2013200385usize),
                (181usize, 268435454usize),
                (177usize, 2013200385usize),
                (178usize, 268435454usize),
                (174usize, 2013200385usize),
                (177usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (170usize, 2013200385usize),
                (173usize, 268435454usize),
                (169usize, 2013200385usize),
                (170usize, 268435454usize),
                (166usize, 2013200385usize),
                (169usize, 268435454usize),
                (208usize, 65536usize),
                (207usize, 65536usize),
                (206usize, 65536usize),
                (205usize, 65536usize),
                (204usize, 65536usize),
                (203usize, 65536usize),
                (202usize, 65536usize),
                (201usize, 65536usize),
                (200usize, 65536usize),
                (199usize, 65536usize),
                (198usize, 65536usize),
                (197usize, 65536usize),
                (196usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (90usize, 2013200385usize),
                (122usize, 65536usize),
                (123usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (169usize, 1usize),
                (170usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (177usize, 1usize),
                (178usize, 1usize),
                (181usize, 1usize),
                (182usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (189usize, 1usize),
                (190usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 81usize] = [
                (71usize, 65536usize),
                (208usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (207usize, 2013200385usize),
                (208usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (206usize, 2013200385usize),
                (207usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (205usize, 2013200385usize),
                (206usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (204usize, 2013200385usize),
                (205usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (202usize, 2013200385usize),
                (203usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (201usize, 2013200385usize),
                (202usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (200usize, 2013200385usize),
                (201usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (199usize, 2013200385usize),
                (200usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (198usize, 2013200385usize),
                (199usize, 268435454usize),
                (60usize, 65536usize),
                (61usize, 1744830467usize),
                (197usize, 2013200385usize),
                (198usize, 268435454usize),
                (190usize, 2013200385usize),
                (189usize, 2013200385usize),
                (190usize, 268435454usize),
                (186usize, 2013200385usize),
                (189usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (182usize, 2013200385usize),
                (185usize, 268435454usize),
                (181usize, 2013200385usize),
                (182usize, 268435454usize),
                (178usize, 2013200385usize),
                (181usize, 268435454usize),
                (177usize, 2013200385usize),
                (178usize, 268435454usize),
                (174usize, 2013200385usize),
                (177usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (170usize, 2013200385usize),
                (173usize, 268435454usize),
                (169usize, 2013200385usize),
                (170usize, 268435454usize),
                (208usize, 65536usize),
                (207usize, 65536usize),
                (206usize, 65536usize),
                (205usize, 65536usize),
                (204usize, 65536usize),
                (203usize, 65536usize),
                (202usize, 65536usize),
                (201usize, 65536usize),
                (200usize, 65536usize),
                (199usize, 65536usize),
                (198usize, 65536usize),
                (197usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (91usize, 2013200385usize),
                (123usize, 65536usize),
                (124usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (170usize, 1usize),
                (173usize, 1usize),
                (174usize, 1usize),
                (177usize, 1usize),
                (178usize, 1usize),
                (181usize, 1usize),
                (182usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (189usize, 1usize),
                (190usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 74usize] = [
                (71usize, 65536usize),
                (208usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (207usize, 2013200385usize),
                (208usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (206usize, 2013200385usize),
                (207usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (205usize, 2013200385usize),
                (206usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (204usize, 2013200385usize),
                (205usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (202usize, 2013200385usize),
                (203usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (201usize, 2013200385usize),
                (202usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (200usize, 2013200385usize),
                (201usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (199usize, 2013200385usize),
                (200usize, 268435454usize),
                (61usize, 65536usize),
                (62usize, 1744830467usize),
                (198usize, 2013200385usize),
                (199usize, 268435454usize),
                (190usize, 2013200385usize),
                (189usize, 2013200385usize),
                (190usize, 268435454usize),
                (186usize, 2013200385usize),
                (189usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (182usize, 2013200385usize),
                (185usize, 268435454usize),
                (181usize, 2013200385usize),
                (182usize, 268435454usize),
                (178usize, 2013200385usize),
                (181usize, 268435454usize),
                (177usize, 2013200385usize),
                (178usize, 268435454usize),
                (174usize, 2013200385usize),
                (177usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (170usize, 2013200385usize),
                (173usize, 268435454usize),
                (208usize, 65536usize),
                (207usize, 65536usize),
                (206usize, 65536usize),
                (205usize, 65536usize),
                (204usize, 65536usize),
                (203usize, 65536usize),
                (202usize, 65536usize),
                (201usize, 65536usize),
                (200usize, 65536usize),
                (199usize, 65536usize),
                (198usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (92usize, 2013200385usize),
                (124usize, 65536usize),
                (125usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (173usize, 1usize),
                (174usize, 1usize),
                (177usize, 1usize),
                (178usize, 1usize),
                (181usize, 1usize),
                (182usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (189usize, 1usize),
                (190usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 67usize] = [
                (71usize, 65536usize),
                (208usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (207usize, 2013200385usize),
                (208usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (206usize, 2013200385usize),
                (207usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (205usize, 2013200385usize),
                (206usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (204usize, 2013200385usize),
                (205usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (202usize, 2013200385usize),
                (203usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (201usize, 2013200385usize),
                (202usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (200usize, 2013200385usize),
                (201usize, 268435454usize),
                (62usize, 65536usize),
                (63usize, 1744830467usize),
                (199usize, 2013200385usize),
                (200usize, 268435454usize),
                (190usize, 2013200385usize),
                (189usize, 2013200385usize),
                (190usize, 268435454usize),
                (186usize, 2013200385usize),
                (189usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (182usize, 2013200385usize),
                (185usize, 268435454usize),
                (181usize, 2013200385usize),
                (182usize, 268435454usize),
                (178usize, 2013200385usize),
                (181usize, 268435454usize),
                (177usize, 2013200385usize),
                (178usize, 268435454usize),
                (174usize, 2013200385usize),
                (177usize, 268435454usize),
                (173usize, 2013200385usize),
                (174usize, 268435454usize),
                (208usize, 65536usize),
                (207usize, 65536usize),
                (206usize, 65536usize),
                (205usize, 65536usize),
                (204usize, 65536usize),
                (203usize, 65536usize),
                (202usize, 65536usize),
                (201usize, 65536usize),
                (200usize, 65536usize),
                (199usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (93usize, 2013200385usize),
                (125usize, 65536usize),
                (126usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (174usize, 1usize),
                (177usize, 1usize),
                (178usize, 1usize),
                (181usize, 1usize),
                (182usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (189usize, 1usize),
                (190usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 60usize] = [
                (71usize, 65536usize),
                (208usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (207usize, 2013200385usize),
                (208usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (206usize, 2013200385usize),
                (207usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (205usize, 2013200385usize),
                (206usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (204usize, 2013200385usize),
                (205usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (202usize, 2013200385usize),
                (203usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (201usize, 2013200385usize),
                (202usize, 268435454usize),
                (63usize, 65536usize),
                (64usize, 1744830467usize),
                (200usize, 2013200385usize),
                (201usize, 268435454usize),
                (190usize, 2013200385usize),
                (189usize, 2013200385usize),
                (190usize, 268435454usize),
                (186usize, 2013200385usize),
                (189usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (182usize, 2013200385usize),
                (185usize, 268435454usize),
                (181usize, 2013200385usize),
                (182usize, 268435454usize),
                (178usize, 2013200385usize),
                (181usize, 268435454usize),
                (177usize, 2013200385usize),
                (178usize, 268435454usize),
                (174usize, 2013200385usize),
                (177usize, 268435454usize),
                (208usize, 65536usize),
                (207usize, 65536usize),
                (206usize, 65536usize),
                (205usize, 65536usize),
                (204usize, 65536usize),
                (203usize, 65536usize),
                (202usize, 65536usize),
                (201usize, 65536usize),
                (200usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (94usize, 2013200385usize),
                (126usize, 65536usize),
                (127usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (177usize, 1usize),
                (178usize, 1usize),
                (181usize, 1usize),
                (182usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (189usize, 1usize),
                (190usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 53usize] = [
                (71usize, 65536usize),
                (208usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (207usize, 2013200385usize),
                (208usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (206usize, 2013200385usize),
                (207usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (205usize, 2013200385usize),
                (206usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (204usize, 2013200385usize),
                (205usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (202usize, 2013200385usize),
                (203usize, 268435454usize),
                (64usize, 65536usize),
                (65usize, 1744830467usize),
                (201usize, 2013200385usize),
                (202usize, 268435454usize),
                (190usize, 2013200385usize),
                (189usize, 2013200385usize),
                (190usize, 268435454usize),
                (186usize, 2013200385usize),
                (189usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (182usize, 2013200385usize),
                (185usize, 268435454usize),
                (181usize, 2013200385usize),
                (182usize, 268435454usize),
                (178usize, 2013200385usize),
                (181usize, 268435454usize),
                (177usize, 2013200385usize),
                (178usize, 268435454usize),
                (208usize, 65536usize),
                (207usize, 65536usize),
                (206usize, 65536usize),
                (205usize, 65536usize),
                (204usize, 65536usize),
                (203usize, 65536usize),
                (202usize, 65536usize),
                (201usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (95usize, 2013200385usize),
                (127usize, 65536usize),
                (128usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (178usize, 1usize),
                (181usize, 1usize),
                (182usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (189usize, 1usize),
                (190usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 46usize] = [
                (71usize, 65536usize),
                (208usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (207usize, 2013200385usize),
                (208usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (206usize, 2013200385usize),
                (207usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (205usize, 2013200385usize),
                (206usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (204usize, 2013200385usize),
                (205usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (65usize, 65536usize),
                (66usize, 1744830467usize),
                (202usize, 2013200385usize),
                (203usize, 268435454usize),
                (190usize, 2013200385usize),
                (189usize, 2013200385usize),
                (190usize, 268435454usize),
                (186usize, 2013200385usize),
                (189usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (182usize, 2013200385usize),
                (185usize, 268435454usize),
                (181usize, 2013200385usize),
                (182usize, 268435454usize),
                (178usize, 2013200385usize),
                (181usize, 268435454usize),
                (208usize, 65536usize),
                (207usize, 65536usize),
                (206usize, 65536usize),
                (205usize, 65536usize),
                (204usize, 65536usize),
                (203usize, 65536usize),
                (202usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (96usize, 2013200385usize),
                (128usize, 65536usize),
                (129usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (181usize, 1usize),
                (182usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (189usize, 1usize),
                (190usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 39usize] = [
                (71usize, 65536usize),
                (208usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (207usize, 2013200385usize),
                (208usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (206usize, 2013200385usize),
                (207usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (205usize, 2013200385usize),
                (206usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (204usize, 2013200385usize),
                (205usize, 268435454usize),
                (66usize, 65536usize),
                (67usize, 1744830467usize),
                (203usize, 2013200385usize),
                (204usize, 268435454usize),
                (190usize, 2013200385usize),
                (189usize, 2013200385usize),
                (190usize, 268435454usize),
                (186usize, 2013200385usize),
                (189usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (182usize, 2013200385usize),
                (185usize, 268435454usize),
                (181usize, 2013200385usize),
                (182usize, 268435454usize),
                (208usize, 65536usize),
                (207usize, 65536usize),
                (206usize, 65536usize),
                (205usize, 65536usize),
                (204usize, 65536usize),
                (203usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (97usize, 2013200385usize),
                (129usize, 65536usize),
                (130usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (182usize, 1usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (189usize, 1usize),
                (190usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 32usize] = [
                (71usize, 65536usize),
                (208usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (207usize, 2013200385usize),
                (208usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (206usize, 2013200385usize),
                (207usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (205usize, 2013200385usize),
                (206usize, 268435454usize),
                (67usize, 65536usize),
                (68usize, 1744830467usize),
                (204usize, 2013200385usize),
                (205usize, 268435454usize),
                (190usize, 2013200385usize),
                (189usize, 2013200385usize),
                (190usize, 268435454usize),
                (186usize, 2013200385usize),
                (189usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (182usize, 2013200385usize),
                (185usize, 268435454usize),
                (208usize, 65536usize),
                (207usize, 65536usize),
                (206usize, 65536usize),
                (205usize, 65536usize),
                (204usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (98usize, 2013200385usize),
                (130usize, 65536usize),
                (131usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 12usize] = [
                (52usize, 2usize),
                (53usize, 4usize),
                (54usize, 4usize),
                (55usize, 4usize),
                (68usize, 1usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (185usize, 1usize),
                (186usize, 1usize),
                (189usize, 1usize),
                (190usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 25usize] = [
                (71usize, 65536usize),
                (208usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (207usize, 2013200385usize),
                (208usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (206usize, 2013200385usize),
                (207usize, 268435454usize),
                (68usize, 65536usize),
                (69usize, 1744830467usize),
                (205usize, 2013200385usize),
                (206usize, 268435454usize),
                (190usize, 2013200385usize),
                (189usize, 2013200385usize),
                (190usize, 268435454usize),
                (186usize, 2013200385usize),
                (189usize, 268435454usize),
                (185usize, 2013200385usize),
                (186usize, 268435454usize),
                (208usize, 65536usize),
                (207usize, 65536usize),
                (206usize, 65536usize),
                (205usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (99usize, 2013200385usize),
                (131usize, 65536usize),
                (132usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 9usize] = [
                (53usize, 2usize),
                (54usize, 4usize),
                (55usize, 4usize),
                (69usize, 1usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (186usize, 1usize),
                (189usize, 1usize),
                (190usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 18usize] = [
                (71usize, 65536usize),
                (208usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (207usize, 2013200385usize),
                (208usize, 268435454usize),
                (69usize, 65536usize),
                (70usize, 1744830467usize),
                (206usize, 2013200385usize),
                (207usize, 268435454usize),
                (190usize, 2013200385usize),
                (189usize, 2013200385usize),
                (190usize, 268435454usize),
                (186usize, 2013200385usize),
                (189usize, 268435454usize),
                (208usize, 65536usize),
                (207usize, 65536usize),
                (206usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (100usize, 2013200385usize),
                (132usize, 65536usize),
                (133usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 6usize] = [
                (54usize, 2usize),
                (55usize, 4usize),
                (70usize, 1usize),
                (71usize, 2usize),
                (189usize, 1usize),
                (190usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 11usize] = [
                (71usize, 65536usize),
                (208usize, 2013200385usize),
                (70usize, 65536usize),
                (71usize, 1744830467usize),
                (207usize, 2013200385usize),
                (208usize, 268435454usize),
                (190usize, 2013200385usize),
                (189usize, 2013200385usize),
                (190usize, 268435454usize),
                (208usize, 65536usize),
                (207usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (101usize, 2013200385usize),
                (133usize, 65536usize),
                (134usize, 1744830467usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 3usize] =
                [(55usize, 2usize), (71usize, 1usize), (190usize, 1usize)];
            const VAL_QI: [(usize, usize); 4usize] = [
                (71usize, 65536usize),
                (208usize, 2013200385usize),
                (190usize, 2013200385usize),
                (208usize, 65536usize),
            ];
            const VAL_LN: [(usize, usize); 3usize] = [
                (102usize, 2013200385usize),
                (103usize, 1744830467usize),
                (134usize, 65536usize),
            ];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (161usize, 268435454usize),
                (8usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(163usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (162usize, 268435454usize),
                (9usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(164usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (165usize, 268435454usize),
                (10usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(167usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (166usize, 268435454usize),
                (11usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(168usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (169usize, 268435454usize),
                (12usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(171usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (170usize, 268435454usize),
                (13usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(172usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (173usize, 268435454usize),
                (14usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(175usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (174usize, 268435454usize),
                (15usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(176usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (177usize, 268435454usize),
                (16usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(179usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (178usize, 268435454usize),
                (17usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(180usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (181usize, 268435454usize),
                (18usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(183usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (182usize, 268435454usize),
                (19usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(184usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (185usize, 268435454usize),
                (20usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(187usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (186usize, 268435454usize),
                (21usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(188usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (189usize, 268435454usize),
                (22usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(191usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                (190usize, 268435454usize),
                (23usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(192usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(39usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(136usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(136usize, 268435454usize), (137usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(137usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(138usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
                [(3usize, 268435454usize), (210usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 1usize] = [(211usize, 268435454usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(0usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(0usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(1usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(1usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(2usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(2usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(3usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(3usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(4usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(4usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(4usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(5usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(5usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(6usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(6usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(7usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(7usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(7usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(24usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(24usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(24usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(25usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(25usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(25usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(26usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(26usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(26usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(27usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(27usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(27usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(28usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(28usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(28usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(29usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(29usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(29usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(30usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(30usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(30usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(31usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(31usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(31usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(32usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(32usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(32usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(33usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(33usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(33usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(34usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(34usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(34usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(35usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(35usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(35usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(36usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(36usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(36usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(37usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(37usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(37usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(38usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(38usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(38usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(39usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(39usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(39usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(136usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(136usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(136usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(139usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(139usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(139usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(140usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(140usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(140usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(141usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(141usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(141usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(142usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(142usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(142usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(143usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(143usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(143usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(144usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(144usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(144usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(145usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(145usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(145usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(146usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(146usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(146usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(147usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(147usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(147usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(148usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(148usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(148usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(149usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(149usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(149usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(150usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(150usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(150usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(151usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(151usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(151usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(152usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(152usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(152usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(153usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(153usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(153usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(154usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(154usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(154usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(155usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(155usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(155usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(156usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(156usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(156usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(157usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(157usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(157usize, 1744830467usize)];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
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
    output_claims: &[BabyBearExt4; 91usize],
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
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_1_final_step_accumulator(
    evals: &[[BabyBearExt4; 1]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    lookup_alpha: BabyBearExt4,
    linearization_challenges: &[BabyBearExt4],
    permutation_argument_additive_part: BabyBearExt4,
    address_high_bits_shift: u32,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 54usize] = [
            (SimpleGateType::Copy, [0usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [1usize, 3usize, 0usize, 0usize]),
            (SimpleGateType::Product, [5usize, 7usize, 0usize, 0usize]),
            (SimpleGateType::Product, [9usize, 11usize, 0usize, 0usize]),
            (SimpleGateType::Product, [13usize, 15usize, 0usize, 0usize]),
            (SimpleGateType::Product, [17usize, 19usize, 0usize, 0usize]),
            (SimpleGateType::Product, [2usize, 4usize, 0usize, 0usize]),
            (SimpleGateType::Product, [6usize, 8usize, 0usize, 0usize]),
            (SimpleGateType::Product, [10usize, 12usize, 0usize, 0usize]),
            (SimpleGateType::Product, [14usize, 16usize, 0usize, 0usize]),
            (SimpleGateType::Product, [18usize, 20usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupInitialPair,
                [21usize, 22usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [23usize, 24usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [25usize, 26usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [27usize, 28usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [29usize, 30usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [31usize, 32usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [33usize, 34usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [35usize, 36usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupUnbalanced,
                [54usize, 55usize, 56usize, 0usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [52usize, 53usize, 50usize, 51usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [48usize, 49usize, 46usize, 47usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [44usize, 45usize, 42usize, 43usize],
            ),
            (SimpleGateType::Copy, [40usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [41usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupUnbalanced,
                [95usize, 96usize, 97usize, 0usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [93usize, 94usize, 91usize, 92usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [89usize, 90usize, 87usize, 88usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [85usize, 86usize, 83usize, 84usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [81usize, 82usize, 79usize, 80usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [77usize, 78usize, 75usize, 76usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [73usize, 74usize, 71usize, 72usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [69usize, 70usize, 67usize, 68usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [65usize, 66usize, 63usize, 64usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [61usize, 62usize, 59usize, 60usize],
            ),
            (SimpleGateType::Copy, [57usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [58usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupAggregatePair,
                [158usize, 159usize, 156usize, 157usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [154usize, 155usize, 152usize, 153usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [150usize, 151usize, 148usize, 149usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [146usize, 147usize, 144usize, 145usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [142usize, 143usize, 140usize, 141usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [138usize, 139usize, 136usize, 137usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [134usize, 135usize, 132usize, 133usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [130usize, 131usize, 128usize, 129usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [126usize, 127usize, 124usize, 125usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [122usize, 123usize, 120usize, 121usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [118usize, 119usize, 116usize, 117usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [114usize, 115usize, 112usize, 113usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [110usize, 111usize, 108usize, 109usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [106usize, 107usize, 104usize, 105usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [102usize, 103usize, 100usize, 101usize],
            ),
            (SimpleGateType::Copy, [98usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [99usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 54usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                SimpleGateType::Copy => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::Product => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::MaskToIdentity => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::UnbalancedProduct => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::LookupInitialPair => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupWithSetup => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupUnbalanced => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupAggregatePair => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupInitialWithCachedDenominators => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
            }
            _sg += 1;
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(37usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(39usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 0usize] = [];
            let val =
                super::common::eval_max_quadratic(evals, &VAL_QO, &VAL_QI, &VAL_LN, 0usize, j);
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(37usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(38usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(39usize, 268435454usize)];
            let val = super::common::eval_max_quadratic(
                evals,
                &VAL_QO,
                &VAL_QI,
                &VAL_LN,
                1744830467usize,
                j,
            );
            let mut contrib = bc;
            field_ops::mul_assign(&mut contrib, &val);
            field_ops::add_assign(&mut acc[j], &contrib);
        }
    }
    acc
}
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_2_compute_claim(
    output_claims: &[BabyBearExt4; 49usize],
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
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_2_final_step_accumulator(
    evals: &[[BabyBearExt4; 1]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    lookup_alpha: BabyBearExt4,
    linearization_challenges: &[BabyBearExt4],
    permutation_argument_additive_part: BabyBearExt4,
    address_high_bits_shift: u32,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 30usize] = [
            (SimpleGateType::Copy, [0usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [1usize, 2usize, 0usize, 0usize]),
            (SimpleGateType::Product, [3usize, 4usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [5usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [6usize, 7usize, 0usize, 0usize]),
            (SimpleGateType::Product, [8usize, 9usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [10usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupAggregatePair,
                [35usize, 36usize, 33usize, 34usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [31usize, 32usize, 29usize, 30usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [27usize, 28usize, 25usize, 26usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [23usize, 24usize, 21usize, 22usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [19usize, 20usize, 17usize, 18usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [15usize, 16usize, 13usize, 14usize],
            ),
            (SimpleGateType::Copy, [11usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [12usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupAggregatePair,
                [57usize, 58usize, 55usize, 56usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [53usize, 54usize, 51usize, 52usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [49usize, 50usize, 47usize, 48usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [45usize, 46usize, 43usize, 44usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [41usize, 42usize, 39usize, 40usize],
            ),
            (SimpleGateType::Copy, [37usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [38usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupAggregatePair,
                [89usize, 90usize, 87usize, 88usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [85usize, 86usize, 83usize, 84usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [81usize, 82usize, 79usize, 80usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [77usize, 78usize, 75usize, 76usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [73usize, 74usize, 71usize, 72usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [69usize, 70usize, 67usize, 68usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [65usize, 66usize, 63usize, 64usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [61usize, 62usize, 59usize, 60usize],
            ),
        ];
        let mut _sg = 0;
        while _sg < 30usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                SimpleGateType::Copy => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::Product => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::MaskToIdentity => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::UnbalancedProduct => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::LookupInitialPair => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupWithSetup => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupUnbalanced => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupAggregatePair => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupInitialWithCachedDenominators => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
            }
            _sg += 1;
        }
    }
    acc
}
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_3_compute_claim(
    output_claims: &[BabyBearExt4; 27usize],
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
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_3_final_step_accumulator(
    evals: &[[BabyBearExt4; 1]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    lookup_alpha: BabyBearExt4,
    linearization_challenges: &[BabyBearExt4],
    permutation_argument_additive_part: BabyBearExt4,
    address_high_bits_shift: u32,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 17usize] = [
            (SimpleGateType::Copy, [0usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [1usize, 2usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [3usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [4usize, 5usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [6usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupAggregatePair,
                [19usize, 20usize, 17usize, 18usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [15usize, 16usize, 13usize, 14usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [11usize, 12usize, 9usize, 10usize],
            ),
            (SimpleGateType::Copy, [7usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [8usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupAggregatePair,
                [31usize, 32usize, 29usize, 30usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [27usize, 28usize, 25usize, 26usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [23usize, 24usize, 21usize, 22usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [47usize, 48usize, 45usize, 46usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [43usize, 44usize, 41usize, 42usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [39usize, 40usize, 37usize, 38usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [35usize, 36usize, 33usize, 34usize],
            ),
        ];
        let mut _sg = 0;
        while _sg < 17usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                SimpleGateType::Copy => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::Product => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::MaskToIdentity => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::UnbalancedProduct => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::LookupInitialPair => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupWithSetup => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupUnbalanced => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupAggregatePair => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupInitialWithCachedDenominators => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
            }
            _sg += 1;
        }
    }
    acc
}
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_4_compute_claim(
    output_claims: &[BabyBearExt4; 15usize],
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
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_4_final_step_accumulator(
    evals: &[[BabyBearExt4; 1]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    lookup_alpha: BabyBearExt4,
    linearization_challenges: &[BabyBearExt4],
    permutation_argument_additive_part: BabyBearExt4,
    address_high_bits_shift: u32,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 10usize] = [
            (SimpleGateType::Copy, [0usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [1usize, 2usize, 0usize, 0usize]),
            (SimpleGateType::Product, [3usize, 4usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupAggregatePair,
                [11usize, 12usize, 9usize, 10usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [7usize, 8usize, 5usize, 6usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [17usize, 18usize, 15usize, 16usize],
            ),
            (SimpleGateType::Copy, [13usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [14usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupAggregatePair,
                [25usize, 26usize, 23usize, 24usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [21usize, 22usize, 19usize, 20usize],
            ),
        ];
        let mut _sg = 0;
        while _sg < 10usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                SimpleGateType::Copy => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::Product => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::MaskToIdentity => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::UnbalancedProduct => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::LookupInitialPair => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupWithSetup => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupUnbalanced => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupAggregatePair => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupInitialWithCachedDenominators => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
            }
            _sg += 1;
        }
    }
    acc
}
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_5_compute_claim(
    output_claims: &[BabyBearExt4; 8usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 5usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (2usize, 2usize, 3usize),
        (2usize, 4usize, 5usize),
        (2usize, 6usize, 7usize),
    ];
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_5_final_step_accumulator(
    evals: &[[BabyBearExt4; 1]],
    batch_base: BabyBearExt4,
    lookup_additive_challenge: BabyBearExt4,
    lookup_alpha: BabyBearExt4,
    linearization_challenges: &[BabyBearExt4],
    permutation_argument_additive_part: BabyBearExt4,
    address_high_bits_shift: u32,
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 5usize] = [
            (
                SimpleGateType::MaskToIdentity,
                [1usize, 0usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::MaskToIdentity,
                [2usize, 0usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [5usize, 6usize, 3usize, 4usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [9usize, 10usize, 7usize, 8usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [13usize, 14usize, 11usize, 12usize],
            ),
        ];
        let mut _sg = 0;
        while _sg < 5usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                SimpleGateType::Copy => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::Product => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vb = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vb);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::MaskToIdentity => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::UnbalancedProduct => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
                        let mut val = evals.get_unchecked(idx[0])[j];
                        let vi = evals.get_unchecked(idx[1])[j];
                        field_ops::mul_assign(&mut val, &vi);
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::LookupInitialPair => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupWithSetup => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupUnbalanced => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupAggregatePair => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
                SimpleGateType::LookupInitialWithCachedDenominators => {
                    let bc0 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    let bc1 = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..1 {
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
            }
            _sg += 1;
        }
    }
    acc
}
#[inline(always)]
#[allow(unused_unsafe)]
unsafe fn dim_reducing_compute_claim(
    output_claims: &[BabyBearExt4; 8usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut current_batch = BabyBearExt4::ONE;
    let combined = {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = *output_claims.get_unchecked(0usize);
        let mut t = bc;
        field_ops::mul_assign(&mut t, &claim);
        t
    };
    let mut combined = combined;
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let claim = *output_claims.get_unchecked(1usize);
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
            let claim = *output_claims.get_unchecked(idx);
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
            let claim = *output_claims.get_unchecked(idx);
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
            let claim = *output_claims.get_unchecked(idx);
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
    evals: &[[BabyBearExt4; 2]],
    batch_base: BabyBearExt4,
    indices: &[usize],
) -> BabyBearExt4 {
    let mut acc = BabyBearExt4::ZERO;
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
        let mut v01 = e0;
        field_ops::mul_assign(&mut v01, &e1);
        let mut c0 = bc;
        field_ops::mul_assign(&mut c0, &v01);
        field_ops::add_assign(&mut acc, &c0);
    }
    {
        let si = unsafe { *indices.get_unchecked(_idx) };
        _idx += 1;
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        let es = unsafe { evals.get_unchecked(si) };
        let e0 = unsafe { *es.get_unchecked(0) };
        let e1 = unsafe { *es.get_unchecked(1) };
        let mut v01 = e0;
        field_ops::mul_assign(&mut v01, &e1);
        let mut c0 = bc;
        field_ops::mul_assign(&mut c0, &v01);
        field_ops::add_assign(&mut acc, &c0);
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
            let v0a = unsafe { *v0.get_unchecked(0) };
            let v0b = unsafe { *v0.get_unchecked(1) };
            let v1a = unsafe { *v1.get_unchecked(0) };
            let v1b = unsafe { *v1.get_unchecked(1) };
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
            field_ops::add_assign(&mut acc, &c0_tmp);
            field_ops::add_assign(&mut acc, &c1_tmp);
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
            let v0a = unsafe { *v0.get_unchecked(0) };
            let v0b = unsafe { *v0.get_unchecked(1) };
            let v1a = unsafe { *v1.get_unchecked(0) };
            let v1b = unsafe { *v1.get_unchecked(1) };
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
            field_ops::add_assign(&mut acc, &c0_tmp);
            field_ops::add_assign(&mut acc, &c1_tmp);
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
            let v0a = unsafe { *v0.get_unchecked(0) };
            let v0b = unsafe { *v0.get_unchecked(1) };
            let v1a = unsafe { *v1.get_unchecked(0) };
            let v1b = unsafe { *v1.get_unchecked(1) };
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
            field_ops::add_assign(&mut acc, &c0_tmp);
            field_ops::add_assign(&mut acc, &c1_tmp);
        }
    }
    acc
}
#[doc = " Closed-form eval of VirtualSetup(RangeCheck16Bits) at `state.prev_point` (lower 16 bits free, top bits forced to zero)."]
#[doc = " Source: prover/src/gkr/virtual_polys/range_check.rs."]
#[doc = " The `prev_claims` index is the position assigned to this VirtualSetup poly by the"]
#[doc = " canonical layer-0 layout (memory cols → witness cols → setup cols → virtual setups → others)."]
#[inline(always)]
fn check_virtual_setup_range_check_16bits<E: ErrorCreator>(
    state: &LayerState<BabyBearExt4, GKR_ROUNDS, GKR_ADDRS>,
) -> Result<(), E::Error> {
    unsafe {
        let pt = state.prev_point.get_unchecked(..22usize);
        let mut result: BabyBearExt4 = BabyBearExt4::ZERO;
        let mut prefactor: BabyBearField = BabyBearField::ONE;
        let mut k: usize = 0;
        while k < 16usize {
            let mut t = *pt.get_unchecked(22usize - 1 - k);
            field_ops::mul_assign_by_base(&mut t, &prefactor);
            field_ops::add_assign(&mut result, &t);
            field_ops::double(&mut prefactor);
            k += 1;
        }
        while k < 22usize {
            let mut t: BabyBearExt4 = BabyBearExt4::ONE;
            let p = pt.get_unchecked(22usize - 1 - k);
            field_ops::sub_assign(&mut t, &*p);
            field_ops::mul_assign(&mut result, &t);
            k += 1;
        }
        if result != *state.prev_claims.get_unchecked(261usize) {
            return Err(E::gkr_virtual_setup_eval_mismatch(261usize));
        }
    }
    Ok(())
}
#[doc = " Closed-form eval of VirtualSetup(RangeCheckTimestamp) at `state.prev_point` (lower 19 bits free, top bits forced to zero)."]
#[doc = " Source: prover/src/gkr/virtual_polys/range_check.rs."]
#[doc = " The `prev_claims` index is the position assigned to this VirtualSetup poly by the"]
#[doc = " canonical layer-0 layout (memory cols → witness cols → setup cols → virtual setups → others)."]
#[inline(always)]
fn check_virtual_setup_range_check_timestamp<E: ErrorCreator>(
    state: &LayerState<BabyBearExt4, GKR_ROUNDS, GKR_ADDRS>,
) -> Result<(), E::Error> {
    unsafe {
        let pt = state.prev_point.get_unchecked(..22usize);
        let mut result: BabyBearExt4 = BabyBearExt4::ZERO;
        let mut prefactor: BabyBearField = BabyBearField::ONE;
        let mut k: usize = 0;
        while k < 19usize {
            let mut t = *pt.get_unchecked(22usize - 1 - k);
            field_ops::mul_assign_by_base(&mut t, &prefactor);
            field_ops::add_assign(&mut result, &t);
            field_ops::double(&mut prefactor);
            k += 1;
        }
        while k < 22usize {
            let mut t: BabyBearExt4 = BabyBearExt4::ONE;
            let p = pt.get_unchecked(22usize - 1 - k);
            field_ops::sub_assign(&mut t, &*p);
            field_ops::mul_assign(&mut result, &t);
            k += 1;
        }
        if result != *state.prev_claims.get_unchecked(262usize) {
            return Err(E::gkr_virtual_setup_eval_mismatch(262usize));
        }
    }
    Ok(())
}
#[allow(unused_variables, unused_mut, unused_unsafe)]
pub(crate) fn verify_gkr<I: NonDeterminismSource, E: ErrorCreator>(
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    initial_transcript: &ConcreteInitialTranscript,
    ts: &mut ::verifier_common::structs::TranscriptState,
    nd_source: &mut I,
) -> Result<ConcreteGKRVerifierOutput, E::Error> {
    unsafe {
        let mut init_challenges = LazyVec::<BabyBearExt4, 2>::new();
        unsafe {
            init_challenges.set_len(2);
        }
        read_and_verify_pow::<I>(ts, LOOKUP_CHALLENGES_POW_BITS, nd_source);
        draw_field_els_into_after_pow::<DRAW_BUF_CAPACITY>(ts, init_challenges.as_mut_slice());
        let lookup_alpha = *init_challenges.get(0);
        let lookup_additive_challenge = *init_challenges.get(1);
        let address_high_bits_shift: u32 = 0u32;
        let mut evals_commit_buf = CommitBuf::<GKR_EVALS_COMMIT_BUF>::new();
        let evals_data_words = 128usize * EXT_DEGREE;
        {
            let mut i = 0;
            while i < evals_data_words {
                evals_commit_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                i += 1;
            }
        }
        ts.commit(&mut evals_commit_buf, evals_data_words);
        let evals_slice: &[BabyBearExt4] = unsafe { evals_commit_buf.data_as(128usize) };
        let mut all_challenges = LazyVec::<BabyBearExt4, { GKR_ROUNDS + 1 }>::new();
        unsafe {
            all_challenges.set_len(5usize);
        }
        draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, all_challenges.as_mut_slice());
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
        #[cfg(feature = "verifier_stats")]
        verifier_common::stats::log("GKR COMPRESSION INIT");
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 4usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    23usize,
                    nd_source,
                )?;
            let mut fc_len = 4usize;
            let data_words = 8usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_23,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 23usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 23");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 5usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    22usize,
                    nd_source,
                )?;
            let mut fc_len = 5usize;
            let data_words = 8usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_22,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 22usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 22");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 6usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    21usize,
                    nd_source,
                )?;
            let mut fc_len = 6usize;
            let data_words = 8usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_21,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 21usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 21");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 7usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    20usize,
                    nd_source,
                )?;
            let mut fc_len = 7usize;
            let data_words = 8usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_20,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 20usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 20");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 8usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    19usize,
                    nd_source,
                )?;
            let mut fc_len = 8usize;
            let data_words = 8usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_19,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 19usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 19");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 9usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    18usize,
                    nd_source,
                )?;
            let mut fc_len = 9usize;
            let data_words = 8usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_18,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 18usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 18");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 10usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    17usize,
                    nd_source,
                )?;
            let mut fc_len = 10usize;
            let data_words = 8usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_17,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 17usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 17");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 11usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    16usize,
                    nd_source,
                )?;
            let mut fc_len = 11usize;
            let data_words = 8usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_16,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 16usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 16");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 12usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    15usize,
                    nd_source,
                )?;
            let mut fc_len = 12usize;
            let data_words = 8usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_15,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 15usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 15");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 13usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    14usize,
                    nd_source,
                )?;
            let mut fc_len = 13usize;
            let data_words = 8usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_14,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 14usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 14");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 14usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    13usize,
                    nd_source,
                )?;
            let mut fc_len = 14usize;
            let data_words = 8usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_13,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 13usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 13");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 15usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    12usize,
                    nd_source,
                )?;
            let mut fc_len = 15usize;
            let data_words = 8usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_12,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 12usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 12");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 16usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    11usize,
                    nd_source,
                )?;
            let mut fc_len = 16usize;
            let data_words = 8usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_11,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 11usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 11");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 17usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    10usize,
                    nd_source,
                )?;
            let mut fc_len = 17usize;
            let data_words = 8usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_10,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 10usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 10");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 18usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    9usize,
                    nd_source,
                )?;
            let mut fc_len = 18usize;
            let data_words = 8usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_9,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 9usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 9");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    8usize,
                    nd_source,
                )?;
            let mut fc_len = 19usize;
            let data_words = 8usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_8,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 8usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 8");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 20usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    7usize,
                    nd_source,
                )?;
            let mut fc_len = 20usize;
            let data_words = 8usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_7,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 7usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 7");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 21usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    6usize,
                    nd_source,
                )?;
            let mut fc_len = 21usize;
            let data_words = 8usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(8usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_6,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 6usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let r_last = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = r_last;
            fc_len += 1;
            const DIM_REDUCING_EXTRA_CHALLENGES: usize = 1;
            const DIM_REDUCING_EQ_SIZE: usize = 1 << DIM_REDUCING_EXTRA_CHALLENGES;
            let mut eq2 = LazyVec::<BabyBearExt4, DIM_REDUCING_EQ_SIZE>::new();
            make_eq_poly(&[r_last], &mut eq2);
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(8usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..8usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 6");
        }
        {
            let initial_claim = layer_5_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 22usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    5usize,
                    nd_source,
                )?;
            let fc_len = 22usize;
            let data_words = 15usize * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(15usize);
                let f = layer_5_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                );
                verify_final_step_check::<E>(f[0], final_eq_prefactor, final_claim, 5usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let next_batching = draw_single_field_el(ts);
            fold_standard_claims::<15usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR MAIN LAYER 5");
        }
        {
            let initial_claim = layer_4_compute_claim(
                state.prev_claims.as_array::<15usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 22usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    4usize,
                    nd_source,
                )?;
            let fc_len = 22usize;
            let data_words = 27usize * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(27usize);
                let f = layer_4_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                );
                verify_final_step_check::<E>(f[0], final_eq_prefactor, final_claim, 4usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let next_batching = draw_single_field_el(ts);
            fold_standard_claims::<27usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR MAIN LAYER 4");
        }
        {
            let initial_claim = layer_3_compute_claim(
                state.prev_claims.as_array::<27usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 22usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    3usize,
                    nd_source,
                )?;
            let fc_len = 22usize;
            let data_words = 49usize * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(49usize);
                let f = layer_3_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                );
                verify_final_step_check::<E>(f[0], final_eq_prefactor, final_claim, 3usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let next_batching = draw_single_field_el(ts);
            fold_standard_claims::<49usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR MAIN LAYER 3");
        }
        {
            let initial_claim = layer_2_compute_claim(
                state.prev_claims.as_array::<49usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 22usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    2usize,
                    nd_source,
                )?;
            let fc_len = 22usize;
            let data_words = 91usize * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(91usize);
                let f = layer_2_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                );
                verify_final_step_check::<E>(f[0], final_eq_prefactor, final_claim, 2usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let next_batching = draw_single_field_el(ts);
            fold_standard_claims::<91usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR MAIN LAYER 2");
        }
        {
            let initial_claim = layer_1_compute_claim(
                state.prev_claims.as_array::<91usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 22usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    1usize,
                    nd_source,
                )?;
            let fc_len = 22usize;
            let data_words = 160usize * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(160usize);
                let f = layer_1_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                );
                verify_final_step_check::<E>(f[0], final_eq_prefactor, final_claim, 1usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let next_batching = draw_single_field_el(ts);
            fold_standard_claims::<160usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR MAIN LAYER 1");
        }
        {
            let initial_claim = layer_0_compute_claim(
                state.prev_claims.as_array::<160usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 22usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    0usize,
                    nd_source,
                )?;
            let fc_len = 22usize;
            let data_words = 357usize * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(357usize);
                let f = layer_0_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                );
                verify_final_step_check::<E>(f[0], final_eq_prefactor, final_claim, 0usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let next_batching = draw_single_field_el(ts);
            const EXTRA_COMMIT_BUF: usize = {
                let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + 46usize * EXT_DEGREE;
                total.div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS) * BLAKE2S_BLOCK_SIZE_U32_WORDS
            };
            let mut extra_buf = CommitBuf::<EXTRA_COMMIT_BUF>::new();
            let extra_data_words = 46usize * EXT_DEGREE;
            {
                let mut i = 0;
                while i < extra_data_words {
                    extra_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            let mut extra_evals = LazyVec::<BabyBearExt4, 46usize>::new();
            {
                let slice: &[BabyBearExt4] = unsafe { extra_buf.data_as(46usize) };
                for el in slice {
                    extra_evals.push(*el);
                }
            }
            ts.commit(&mut extra_buf, extra_data_words);
            let final_step_evals: &[[BabyBearExt4; 1]] = unsafe { eval_buf.data_as(357usize) };
            state.prev_claims.clear();
            {
                const LAYOUT_KIND: [usize; 403usize] = [
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize,
                    1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize,
                    0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize,
                    1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize,
                    1usize, 1usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 1usize, 1usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    1usize, 1usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 1usize, 1usize,
                    0usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize,
                    1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize,
                ];
                const LAYOUT_POS: [usize; 403usize] = [
                    0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 161usize, 162usize, 163usize,
                    164usize, 6usize, 7usize, 165usize, 166usize, 167usize, 168usize, 8usize,
                    9usize, 169usize, 170usize, 171usize, 172usize, 10usize, 11usize, 173usize,
                    174usize, 175usize, 176usize, 12usize, 13usize, 177usize, 178usize, 179usize,
                    180usize, 14usize, 15usize, 181usize, 182usize, 183usize, 184usize, 16usize,
                    17usize, 185usize, 186usize, 187usize, 188usize, 18usize, 19usize, 189usize,
                    190usize, 191usize, 192usize, 20usize, 21usize, 22usize, 23usize, 24usize,
                    25usize, 193usize, 194usize, 26usize, 27usize, 195usize, 196usize, 28usize,
                    29usize, 197usize, 198usize, 30usize, 31usize, 199usize, 200usize, 32usize,
                    33usize, 201usize, 202usize, 34usize, 35usize, 203usize, 204usize, 36usize,
                    37usize, 205usize, 206usize, 38usize, 39usize, 207usize, 208usize, 40usize,
                    41usize, 209usize, 42usize, 210usize, 211usize, 212usize, 213usize, 214usize,
                    0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize,
                    10usize, 11usize, 12usize, 13usize, 14usize, 15usize, 16usize, 17usize,
                    18usize, 19usize, 20usize, 21usize, 22usize, 23usize, 24usize, 25usize,
                    26usize, 27usize, 28usize, 29usize, 30usize, 31usize, 32usize, 33usize,
                    34usize, 35usize, 36usize, 37usize, 38usize, 39usize, 40usize, 41usize,
                    42usize, 43usize, 44usize, 45usize, 46usize, 47usize, 48usize, 49usize,
                    50usize, 51usize, 52usize, 53usize, 54usize, 55usize, 56usize, 57usize,
                    58usize, 59usize, 60usize, 61usize, 62usize, 63usize, 64usize, 65usize,
                    66usize, 67usize, 68usize, 69usize, 70usize, 71usize, 72usize, 73usize,
                    74usize, 75usize, 76usize, 77usize, 78usize, 79usize, 80usize, 81usize,
                    82usize, 83usize, 84usize, 85usize, 86usize, 87usize, 88usize, 89usize,
                    90usize, 91usize, 92usize, 93usize, 94usize, 95usize, 96usize, 97usize,
                    98usize, 99usize, 100usize, 101usize, 102usize, 103usize, 104usize, 105usize,
                    106usize, 107usize, 108usize, 109usize, 110usize, 111usize, 112usize, 113usize,
                    114usize, 115usize, 116usize, 117usize, 118usize, 119usize, 120usize, 121usize,
                    122usize, 123usize, 124usize, 125usize, 126usize, 127usize, 128usize, 129usize,
                    130usize, 131usize, 132usize, 133usize, 134usize, 135usize, 136usize, 137usize,
                    138usize, 139usize, 140usize, 141usize, 142usize, 143usize, 144usize, 145usize,
                    146usize, 147usize, 148usize, 149usize, 150usize, 151usize, 152usize, 153usize,
                    154usize, 155usize, 156usize, 157usize, 158usize, 159usize, 160usize, 43usize,
                    44usize, 45usize, 215usize, 216usize, 217usize, 218usize, 219usize, 220usize,
                    221usize, 222usize, 223usize, 224usize, 225usize, 226usize, 227usize, 228usize,
                    229usize, 230usize, 231usize, 232usize, 233usize, 234usize, 235usize, 236usize,
                    237usize, 238usize, 239usize, 240usize, 241usize, 242usize, 243usize, 244usize,
                    245usize, 246usize, 247usize, 248usize, 249usize, 250usize, 251usize, 252usize,
                    253usize, 254usize, 255usize, 256usize, 257usize, 258usize, 259usize, 260usize,
                    261usize, 262usize, 263usize, 264usize, 265usize, 266usize, 267usize, 268usize,
                    269usize, 270usize, 271usize, 272usize, 273usize, 274usize, 275usize, 276usize,
                    277usize, 278usize, 279usize, 280usize, 281usize, 282usize, 283usize, 284usize,
                    285usize, 286usize, 287usize, 288usize, 289usize, 290usize, 291usize, 292usize,
                    293usize, 294usize, 295usize, 296usize, 297usize, 298usize, 299usize, 300usize,
                    301usize, 302usize, 303usize, 304usize, 305usize, 306usize, 307usize, 308usize,
                    309usize, 310usize, 311usize, 312usize, 313usize, 314usize, 315usize, 316usize,
                    317usize, 318usize, 319usize, 320usize, 321usize, 322usize, 323usize, 324usize,
                    325usize, 326usize, 327usize, 328usize, 329usize, 330usize, 331usize, 332usize,
                    333usize, 334usize, 335usize, 336usize, 337usize, 338usize, 339usize, 340usize,
                    341usize, 342usize, 343usize, 344usize, 345usize, 346usize, 347usize, 348usize,
                    349usize, 350usize, 351usize, 352usize, 353usize, 354usize, 355usize, 356usize,
                ];
                let mut i = 0usize;
                while i < 403usize {
                    let kind = unsafe { *LAYOUT_KIND.get_unchecked(i) };
                    let pos = unsafe { *LAYOUT_POS.get_unchecked(i) };
                    let claim: BabyBearExt4 = if kind == 0usize {
                        unsafe { final_step_evals.get_unchecked(pos)[0] }
                    } else {
                        *extra_evals.get(pos)
                    };
                    state.prev_claims.push(claim);
                    i += 1;
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
                    (1744830467u32, 95usize),
                    (268435454u32, 0usize),
                    (133099247u32, 236usize),
                    (1744830467u32, 96usize),
                    (268435454u32, 1usize),
                    (1744830467u32, 236usize),
                    (1744830467u32, 95usize),
                    (268435454u32, 4usize),
                    (133099247u32, 237usize),
                    (1744830467u32, 96usize),
                    (268435454u32, 5usize),
                    (1744830467u32, 237usize),
                    (1744830467u32, 95usize),
                    (268435454u32, 10usize),
                    (133099247u32, 238usize),
                    (1744830467u32, 96usize),
                    (268435454u32, 11usize),
                    (1744830467u32, 238usize),
                    (1744830467u32, 95usize),
                    (268435454u32, 16usize),
                    (133099247u32, 239usize),
                    (1744830467u32, 96usize),
                    (268435454u32, 17usize),
                    (1744830467u32, 239usize),
                    (1744830467u32, 95usize),
                    (268435454u32, 22usize),
                    (133099247u32, 240usize),
                    (1744830467u32, 96usize),
                    (268435454u32, 23usize),
                    (1744830467u32, 240usize),
                    (1744830467u32, 95usize),
                    (268435454u32, 28usize),
                    (133099247u32, 241usize),
                    (1744830467u32, 96usize),
                    (268435454u32, 29usize),
                    (1744830467u32, 241usize),
                    (1744830467u32, 95usize),
                    (268435454u32, 34usize),
                    (133099247u32, 242usize),
                    (1744830467u32, 96usize),
                    (268435454u32, 35usize),
                    (1744830467u32, 242usize),
                    (1744830467u32, 95usize),
                    (268435454u32, 40usize),
                    (133099247u32, 243usize),
                    (1744830467u32, 96usize),
                    (268435454u32, 41usize),
                    (1744830467u32, 243usize),
                    (1744830467u32, 95usize),
                    (268435454u32, 46usize),
                    (133099247u32, 244usize),
                    (1744830467u32, 96usize),
                    (268435454u32, 47usize),
                    (1744830467u32, 244usize),
                    (1744830467u32, 95usize),
                    (268435454u32, 52usize),
                    (133099247u32, 245usize),
                    (1744830467u32, 96usize),
                    (268435454u32, 53usize),
                    (1744830467u32, 245usize),
                    (1744830467u32, 95usize),
                    (268435454u32, 56usize),
                    (133099247u32, 246usize),
                    (1744830467u32, 96usize),
                    (268435454u32, 57usize),
                    (1744830467u32, 246usize),
                    (1744830467u32, 95usize),
                    (268435454u32, 60usize),
                    (133099247u32, 247usize),
                    (1744830467u32, 96usize),
                    (268435454u32, 61usize),
                    (1744830467u32, 247usize),
                    (1744830467u32, 95usize),
                    (268435454u32, 64usize),
                    (133099247u32, 248usize),
                    (1744830467u32, 96usize),
                    (268435454u32, 65usize),
                    (1744830467u32, 248usize),
                    (1744830467u32, 95usize),
                    (268435454u32, 68usize),
                    (133099247u32, 249usize),
                    (1744830467u32, 96usize),
                    (268435454u32, 69usize),
                    (1744830467u32, 249usize),
                    (1744830467u32, 95usize),
                    (268435454u32, 72usize),
                    (133099247u32, 250usize),
                    (1744830467u32, 96usize),
                    (268435454u32, 73usize),
                    (1744830467u32, 250usize),
                    (1744830467u32, 95usize),
                    (268435454u32, 76usize),
                    (133099247u32, 251usize),
                    (1744830467u32, 96usize),
                    (268435454u32, 77usize),
                    (1744830467u32, 251usize),
                    (1744830467u32, 95usize),
                    (268435454u32, 80usize),
                    (133099247u32, 252usize),
                    (1744830467u32, 96usize),
                    (268435454u32, 81usize),
                    (1744830467u32, 252usize),
                    (1744830467u32, 95usize),
                    (268435454u32, 84usize),
                    (133099247u32, 253usize),
                    (1744830467u32, 96usize),
                    (268435454u32, 85usize),
                    (1744830467u32, 253usize),
                    (1744830467u32, 95usize),
                    (268435454u32, 88usize),
                    (133099247u32, 254usize),
                    (1744830467u32, 96usize),
                    (268435454u32, 89usize),
                    (1744830467u32, 254usize),
                ];
                let mut _sc = 0;
                while _sc < 38usize {
                    let (cached_idx, constant, term_start, term_count) = SC_DESCS[_sc];
                    let mut expected: BabyBearExt4 =
                        BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(constant));
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
                        return Err(E::gkr_single_lookup_cache_relation_failed(0usize, _sc));
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
                    (268435454u32, 6usize),
                    (268435454u32, 137usize),
                    (268435454u32, 7usize),
                    (268435454u32, 138usize),
                    (268435454u32, 12usize),
                    (268435454u32, 139usize),
                    (268435454u32, 13usize),
                    (268435454u32, 140usize),
                    (268435454u32, 18usize),
                    (268435454u32, 141usize),
                    (268435454u32, 19usize),
                    (268435454u32, 142usize),
                    (268435454u32, 24usize),
                    (268435454u32, 143usize),
                    (268435454u32, 25usize),
                    (268435454u32, 144usize),
                    (268435454u32, 30usize),
                    (268435454u32, 145usize),
                    (268435454u32, 31usize),
                    (268435454u32, 146usize),
                    (268435454u32, 36usize),
                    (268435454u32, 147usize),
                    (268435454u32, 37usize),
                    (268435454u32, 148usize),
                    (268435454u32, 42usize),
                    (268435454u32, 149usize),
                    (268435454u32, 43usize),
                    (268435454u32, 150usize),
                    (268435454u32, 48usize),
                    (268435454u32, 151usize),
                    (268435454u32, 49usize),
                    (268435454u32, 152usize),
                    (268435454u32, 58usize),
                    (268435454u32, 153usize),
                    (268435454u32, 59usize),
                    (268435454u32, 154usize),
                    (268435454u32, 62usize),
                    (268435454u32, 155usize),
                    (268435454u32, 63usize),
                    (268435454u32, 156usize),
                    (268435454u32, 66usize),
                    (268435454u32, 157usize),
                    (268435454u32, 67usize),
                    (268435454u32, 158usize),
                    (268435454u32, 70usize),
                    (268435454u32, 159usize),
                    (268435454u32, 71usize),
                    (268435454u32, 160usize),
                    (268435454u32, 74usize),
                    (268435454u32, 161usize),
                    (268435454u32, 75usize),
                    (268435454u32, 162usize),
                    (268435454u32, 78usize),
                    (268435454u32, 163usize),
                    (268435454u32, 79usize),
                    (268435454u32, 164usize),
                    (268435454u32, 82usize),
                    (268435454u32, 165usize),
                    (268435454u32, 83usize),
                    (268435454u32, 166usize),
                    (268435454u32, 86usize),
                    (268435454u32, 167usize),
                    (268435454u32, 87usize),
                    (268435454u32, 168usize),
                    (2013200385u32, 169usize),
                    (65536u32, 201usize),
                    (2013200385u32, 199usize),
                    (65536u32, 231usize),
                    (2013200385u32, 170usize),
                    (65536u32, 202usize),
                    (2013200385u32, 198usize),
                    (65536u32, 230usize),
                    (2013200385u32, 171usize),
                    (65536u32, 203usize),
                    (2013200385u32, 172usize),
                    (65536u32, 204usize),
                    (2013200385u32, 196usize),
                    (65536u32, 228usize),
                    (2013200385u32, 197usize),
                    (65536u32, 229usize),
                    (2013200385u32, 173usize),
                    (65536u32, 205usize),
                    (2013200385u32, 174usize),
                    (65536u32, 206usize),
                    (2013200385u32, 175usize),
                    (65536u32, 207usize),
                    (2013200385u32, 176usize),
                    (65536u32, 208usize),
                    (2013200385u32, 192usize),
                    (65536u32, 224usize),
                    (2013200385u32, 193usize),
                    (65536u32, 225usize),
                    (2013200385u32, 194usize),
                    (65536u32, 226usize),
                    (2013200385u32, 195usize),
                    (65536u32, 227usize),
                    (2013200385u32, 177usize),
                    (65536u32, 209usize),
                    (2013200385u32, 178usize),
                    (65536u32, 210usize),
                    (2013200385u32, 179usize),
                    (65536u32, 211usize),
                    (2013200385u32, 180usize),
                    (65536u32, 212usize),
                    (2013200385u32, 181usize),
                    (65536u32, 213usize),
                    (2013200385u32, 182usize),
                    (65536u32, 214usize),
                    (2013200385u32, 183usize),
                    (65536u32, 215usize),
                    (2013200385u32, 184usize),
                    (65536u32, 216usize),
                    (2013200385u32, 185usize),
                    (65536u32, 217usize),
                    (2013200385u32, 186usize),
                    (65536u32, 218usize),
                    (2013200385u32, 187usize),
                    (65536u32, 219usize),
                    (2013200385u32, 188usize),
                    (65536u32, 220usize),
                    (2013200385u32, 189usize),
                    (65536u32, 221usize),
                    (2013200385u32, 190usize),
                    (65536u32, 222usize),
                    (2013200385u32, 191usize),
                    (65536u32, 223usize),
                ];
                let mut _vl = 0;
                while _vl < 61usize {
                    let (cached_idx, col_start, col_count) = VL_DESCS[_vl];
                    let mut expected: BabyBearExt4 = BabyBearExt4::ZERO;
                    let mut alpha_power: BabyBearExt4 = BabyBearExt4::ONE;
                    let mut _c = 0;
                    while _c < col_count {
                        let (col_constant, term_start, term_count) = VL_COLS[col_start + _c];
                        let mut col_val: BabyBearExt4 = BabyBearExt4::from_base(
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
                        return Err(E::gkr_vector_lookup_cache_relation_failed(0usize, _vl));
                    }
                    _vl += 1;
                }
            }
            {
                const VS_DESCS: [(usize, usize, usize); 1usize] = [(342usize, 0usize, 3usize)];
                const VS_DEPS: [usize; 3usize] = [258usize, 259usize, 260usize];
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
                        return Err(E::gkr_permutation_cache_relation_failed(0usize, _vs));
                    }
                    _vs += 1;
                }
            }
            check_virtual_setup_range_check_16bits::<E>(&state)?;
            check_virtual_setup_range_check_timestamp::<E>(&state)?;
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR MAIN LAYER 0");
        }
        read_and_verify_pow::<I>(ts, BATCHED_PROXIMITY_POW_BITS, nd_source);
        state.batching_challenge = draw_single_field_el_after_pow(ts);
        let mut permutation_read_product: BabyBearExt4 = BabyBearExt4::ONE;
        let mut permutation_write_product: BabyBearExt4 = BabyBearExt4::ONE;
        {
            let mut read_product = BabyBearExt4::ONE;
            for i in 0..16usize {
                let eval = *evals_slice.get_unchecked(0usize + i);
                field_ops::mul_assign(&mut read_product, &eval);
            }
            let mut write_product = BabyBearExt4::ONE;
            for i in 0..16usize {
                let eval = *evals_slice.get_unchecked(16usize + i);
                field_ops::mul_assign(&mut write_product, &eval);
            }
            permutation_read_product = read_product;
            permutation_write_product = write_product;
        }
        {
            let mut acc_num = BabyBearExt4::ZERO;
            let mut acc_den = BabyBearExt4::ONE;
            for i in 0..16usize {
                let n = *evals_slice.get_unchecked(32usize + i);
                let d = *evals_slice.get_unchecked(48usize + i);
                field_ops::mul_assign(&mut acc_num, &d);
                let mut t = n;
                field_ops::mul_assign(&mut t, &acc_den);
                field_ops::add_assign(&mut acc_num, &t);
                field_ops::mul_assign(&mut acc_den, &d);
            }
            if !acc_num.is_zero() || acc_den.is_zero() {
                return Err(E::gkr_lookup_identity_failed(0usize));
            }
        }
        {
            let mut acc_num = BabyBearExt4::ZERO;
            let mut acc_den = BabyBearExt4::ONE;
            for i in 0..16usize {
                let n = *evals_slice.get_unchecked(64usize + i);
                let d = *evals_slice.get_unchecked(80usize + i);
                field_ops::mul_assign(&mut acc_num, &d);
                let mut t = n;
                field_ops::mul_assign(&mut t, &acc_den);
                field_ops::add_assign(&mut acc_num, &t);
                field_ops::mul_assign(&mut acc_den, &d);
            }
            if !acc_num.is_zero() || acc_den.is_zero() {
                return Err(E::gkr_lookup_identity_failed(1usize));
            }
        }
        {
            let mut acc_num = BabyBearExt4::ZERO;
            let mut acc_den = BabyBearExt4::ONE;
            for i in 0..16usize {
                let n = *evals_slice.get_unchecked(96usize + i);
                let d = *evals_slice.get_unchecked(112usize + i);
                field_ops::mul_assign(&mut acc_num, &d);
                let mut t = n;
                field_ops::mul_assign(&mut t, &acc_den);
                field_ops::add_assign(&mut acc_num, &t);
                field_ops::mul_assign(&mut acc_den, &d);
            }
            if !acc_num.is_zero() || acc_den.is_zero() {
                return Err(E::gkr_lookup_identity_failed(2usize));
            }
        }
        #[cfg(feature = "verifier_stats")]
        verifier_common::stats::log("GKR MAIN OUTPUT");
        Ok(GKRVerifierOutput {
            base_layer_claims: state.prev_claims,
            evaluation_point: state.prev_point,
            evaluation_point_len: state.prev_point_len,
            permutation_read_product,
            permutation_write_product,
            whir_batching_challenge: state.batching_challenge,
        })
    }
}
pub struct VerifierImplementation;
impl
    ::verifier_common::ConcreteVerifierImpl<
        BabyBearField,
        BabyBearExt4,
        INIT_AND_TEARDOWN_SETS,
        EXTERNAL_CHALLENGES_FLATTENED_SIZE,
        CAP_SIZE,
        NUM_MEMORY_COMMITS,
        NUM_WITNESS_COMMITS,
        NUM_SETUP_COMMITS,
        PADDING_WORDS,
        GKR_ROUNDS,
        GKR_ADDRS,
    > for VerifierImplementation
{
    #[inline(always)]
    fn verify_gkr<I: NonDeterminismSource, E: ErrorCreator>(
        external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
        initial_transcript: &ConcreteInitialTranscript,
        transcript_state: &mut ::verifier_common::structs::TranscriptState,
        nd_source: &mut I,
    ) -> Result<ConcreteGKRVerifierOutput, E::Error> {
        verify_gkr::<I, E>(
            external_challenges,
            initial_transcript,
            transcript_state,
            nd_source,
        )
    }
    #[inline(always)]
    fn verify_whir<I: NonDeterminismSource, E: ErrorCreator>(
        initial_transcript: &ConcreteInitialTranscript,
        transcript_state: &mut ::verifier_common::structs::TranscriptState,
        whir_batching_challenge: BabyBearExt4,
        base_layer_claims: &[BabyBearExt4],
        initial_claim_point: &[BabyBearExt4],
        nd_source: &mut I,
    ) -> Result<(), E::Error> {
        super::whir::verify_whir::<I, E>(
            initial_transcript,
            transcript_state,
            whir_batching_challenge,
            base_layer_claims,
            initial_claim_point,
            nd_source,
        )
    }
}
