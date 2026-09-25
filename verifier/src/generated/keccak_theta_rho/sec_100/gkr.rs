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
    output_claims: &[BabyBearExt4; 115usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 115usize] = [
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
        (2usize, 47usize, 48usize),
        (2usize, 49usize, 50usize),
        (2usize, 51usize, 52usize),
        (2usize, 53usize, 54usize),
        (1usize, 55usize, 0usize),
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
        (2usize, 90usize, 91usize),
        (2usize, 92usize, 93usize),
        (2usize, 94usize, 95usize),
        (2usize, 96usize, 97usize),
        (2usize, 98usize, 99usize),
        (2usize, 100usize, 101usize),
        (2usize, 102usize, 103usize),
        (2usize, 104usize, 105usize),
        (2usize, 106usize, 107usize),
        (2usize, 108usize, 109usize),
        (2usize, 110usize, 111usize),
        (2usize, 112usize, 113usize),
        (1usize, 114usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
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
    inits_and_teardowns_top_bits: &[u32],
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 67usize] = [
            (SimpleGateType::Copy, [146usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::Product,
                [151usize, 152usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [153usize, 154usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [155usize, 156usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [157usize, 158usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [159usize, 160usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [161usize, 162usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [163usize, 164usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [165usize, 166usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [167usize, 168usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [169usize, 170usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [171usize, 172usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [173usize, 174usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [175usize, 176usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [177usize, 178usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [179usize, 180usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [181usize, 182usize, 0usize, 0usize],
            ),
            (SimpleGateType::Copy, [183usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [184usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupWithSetup,
                [185usize, 104usize, 149usize, 0usize],
            ),
            (
                SimpleGateType::LookupWithSetup,
                [147usize, 105usize, 150usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [148usize, 186usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [187usize, 188usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [189usize, 190usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [191usize, 192usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [193usize, 194usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [195usize, 196usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [197usize, 198usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [199usize, 200usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [201usize, 202usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [203usize, 204usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [205usize, 206usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [207usize, 208usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [209usize, 210usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [211usize, 212usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [213usize, 214usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [215usize, 216usize, 0usize, 0usize],
            ),
            (SimpleGateType::Copy, [217usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupWithSetup,
                [218usize, 106usize, 219usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [220usize, 221usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [222usize, 223usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [224usize, 225usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [226usize, 227usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [228usize, 229usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [230usize, 231usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [232usize, 233usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [234usize, 235usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [236usize, 237usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [238usize, 239usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [240usize, 241usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [242usize, 243usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [244usize, 245usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [246usize, 247usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [248usize, 249usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [250usize, 251usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [252usize, 253usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [254usize, 255usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [256usize, 257usize, 0usize, 0usize],
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
        ];
        let mut _sg = 0;
        while _sg < 67usize {
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
            const VAL_COLS: [(usize, usize); 9usize] = [
                (671088523usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 1usize),
                (0usize, 4usize),
                (0usize, 2usize),
                (0usize, 2usize),
            ];
            const VAL_VL_TERMS: [(usize, usize); 10usize] = [
                (87usize, 268435454usize),
                (86usize, 268435454usize),
                (2usize, 536870908usize),
                (3usize, 536870908usize),
                (4usize, 1342177270usize),
                (6usize, 1610612724usize),
                (0usize, 268435454usize),
                (1usize, 268435422usize),
                (127usize, 16777216usize),
                (71usize, 1996488705usize),
            ];
            let mut val =
                super::common::eval_vector_lookup(evals, lookup_alpha, &VAL_COLS, &VAL_VL_TERMS, j);
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 1usize] = [(107usize, 268435454usize)];
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
            const VAL_LN: [(usize, usize); 1usize] = [(108usize, 268435454usize)];
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
            const VAL_LN: [(usize, usize); 2usize] =
                [(130usize, 1744830467usize), (132usize, 268435454usize)];
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
            const VAL_LN: [(usize, usize); 2usize] =
                [(131usize, 1744830467usize), (133usize, 268435454usize)];
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
            const VAL_LN: [(usize, usize); 2usize] =
                [(134usize, 1744830467usize), (136usize, 268435454usize)];
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
            const VAL_LN: [(usize, usize); 2usize] =
                [(135usize, 1744830467usize), (137usize, 268435454usize)];
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
            const VAL_LN: [(usize, usize); 2usize] =
                [(138usize, 1744830467usize), (140usize, 268435454usize)];
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
            const VAL_LN: [(usize, usize); 2usize] =
                [(139usize, 1744830467usize), (141usize, 268435454usize)];
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
            const VAL_LN: [(usize, usize); 2usize] =
                [(142usize, 1744830467usize), (144usize, 268435454usize)];
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
            const VAL_LN: [(usize, usize); 2usize] =
                [(143usize, 1744830467usize), (145usize, 268435454usize)];
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
                (2usize, 2usize),
                (3usize, 4usize),
                (4usize, 4usize),
                (5usize, 4usize),
                (6usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 18usize] = [
                (7usize, 268435454usize),
                (9usize, 268434910usize),
                (7usize, 268435454usize),
                (8usize, 268434910usize),
                (9usize, 268434910usize),
                (22usize, 268435454usize),
                (8usize, 268435454usize),
                (9usize, 268435454usize),
                (10usize, 268434910usize),
                (11usize, 268434910usize),
                (16usize, 268435454usize),
                (17usize, 268435454usize),
                (18usize, 268434910usize),
                (19usize, 268434910usize),
                (16usize, 268435454usize),
                (17usize, 268435454usize),
                (18usize, 268434910usize),
                (19usize, 268434910usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(109usize, 1744830467usize)];
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
                (2usize, 2usize),
                (3usize, 4usize),
                (4usize, 4usize),
                (5usize, 4usize),
                (6usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 18usize] = [
                (11usize, 268435454usize),
                (13usize, 268434910usize),
                (10usize, 268435454usize),
                (11usize, 268435454usize),
                (12usize, 268434910usize),
                (13usize, 268434910usize),
                (12usize, 268435454usize),
                (13usize, 268435454usize),
                (14usize, 268434910usize),
                (15usize, 268434910usize),
                (7usize, 268434910usize),
                (20usize, 268435454usize),
                (21usize, 268435454usize),
                (22usize, 268434910usize),
                (7usize, 268434910usize),
                (20usize, 268435454usize),
                (21usize, 268435454usize),
                (22usize, 268434910usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(110usize, 1744830467usize)];
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
                (2usize, 2usize),
                (3usize, 4usize),
                (4usize, 4usize),
                (5usize, 4usize),
                (6usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 18usize] = [
                (15usize, 268435454usize),
                (17usize, 268434910usize),
                (14usize, 268435454usize),
                (15usize, 268435454usize),
                (16usize, 268434910usize),
                (17usize, 268434910usize),
                (16usize, 268435454usize),
                (17usize, 268435454usize),
                (18usize, 268434910usize),
                (19usize, 268434910usize),
                (8usize, 268435454usize),
                (9usize, 268435454usize),
                (10usize, 268434910usize),
                (11usize, 268434910usize),
                (8usize, 268435454usize),
                (9usize, 268435454usize),
                (10usize, 268434910usize),
                (11usize, 268434910usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(111usize, 1744830467usize)];
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
                (2usize, 2usize),
                (3usize, 4usize),
                (4usize, 4usize),
                (5usize, 4usize),
                (6usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 18usize] = [
                (19usize, 268435454usize),
                (21usize, 268434910usize),
                (18usize, 268435454usize),
                (19usize, 268435454usize),
                (20usize, 268434910usize),
                (21usize, 268434910usize),
                (7usize, 268434910usize),
                (20usize, 268435454usize),
                (21usize, 268435454usize),
                (22usize, 268434910usize),
                (12usize, 268435454usize),
                (13usize, 268435454usize),
                (14usize, 268434910usize),
                (15usize, 268434910usize),
                (12usize, 268435454usize),
                (13usize, 268435454usize),
                (14usize, 268434910usize),
                (15usize, 268434910usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(112usize, 1744830467usize)];
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
                (2usize, 4usize),
                (3usize, 4usize),
                (4usize, 4usize),
                (5usize, 4usize),
                (6usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 20usize] = [
                (30usize, 268435454usize),
                (31usize, 268435454usize),
                (32usize, 268434910usize),
                (33usize, 268434910usize),
                (28usize, 268435454usize),
                (29usize, 268435454usize),
                (30usize, 268434910usize),
                (31usize, 268434910usize),
                (23usize, 268435454usize),
                (24usize, 268434910usize),
                (25usize, 268434910usize),
                (38usize, 268435454usize),
                (26usize, 268435454usize),
                (27usize, 268435454usize),
                (28usize, 268434910usize),
                (29usize, 268434910usize),
                (34usize, 268435454usize),
                (35usize, 268435454usize),
                (36usize, 268434910usize),
                (37usize, 268434910usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(113usize, 1744830467usize)];
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
                (2usize, 4usize),
                (3usize, 4usize),
                (4usize, 4usize),
                (5usize, 4usize),
                (6usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 20usize] = [
                (34usize, 268435454usize),
                (35usize, 268435454usize),
                (36usize, 268434910usize),
                (37usize, 268434910usize),
                (32usize, 268435454usize),
                (33usize, 268435454usize),
                (34usize, 268434910usize),
                (35usize, 268434910usize),
                (26usize, 268435454usize),
                (27usize, 268435454usize),
                (28usize, 268434910usize),
                (29usize, 268434910usize),
                (30usize, 268435454usize),
                (31usize, 268435454usize),
                (32usize, 268434910usize),
                (33usize, 268434910usize),
                (23usize, 268435454usize),
                (24usize, 268434910usize),
                (25usize, 268434910usize),
                (38usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(114usize, 1744830467usize)];
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
                (2usize, 4usize),
                (3usize, 4usize),
                (4usize, 4usize),
                (5usize, 4usize),
                (6usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 20usize] = [
                (23usize, 268435454usize),
                (24usize, 268434910usize),
                (25usize, 268434910usize),
                (38usize, 268435454usize),
                (23usize, 268434910usize),
                (36usize, 268435454usize),
                (37usize, 268435454usize),
                (38usize, 268434910usize),
                (30usize, 268435454usize),
                (31usize, 268435454usize),
                (32usize, 268434910usize),
                (33usize, 268434910usize),
                (34usize, 268435454usize),
                (35usize, 268435454usize),
                (36usize, 268434910usize),
                (37usize, 268434910usize),
                (26usize, 268435454usize),
                (27usize, 268435454usize),
                (28usize, 268434910usize),
                (29usize, 268434910usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(115usize, 1744830467usize)];
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
                (2usize, 4usize),
                (3usize, 4usize),
                (4usize, 4usize),
                (5usize, 4usize),
                (6usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 20usize] = [
                (26usize, 268435454usize),
                (27usize, 268435454usize),
                (28usize, 268434910usize),
                (29usize, 268434910usize),
                (24usize, 268435454usize),
                (25usize, 268435454usize),
                (26usize, 268434910usize),
                (27usize, 268434910usize),
                (34usize, 268435454usize),
                (35usize, 268435454usize),
                (36usize, 268434910usize),
                (37usize, 268434910usize),
                (23usize, 268435454usize),
                (24usize, 268434910usize),
                (25usize, 268434910usize),
                (38usize, 268435454usize),
                (30usize, 268435454usize),
                (31usize, 268435454usize),
                (32usize, 268434910usize),
                (33usize, 268434910usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(116usize, 1744830467usize)];
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
                (2usize, 4usize),
                (3usize, 4usize),
                (4usize, 4usize),
                (5usize, 4usize),
                (6usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 20usize] = [
                (39usize, 268435454usize),
                (40usize, 268434910usize),
                (41usize, 268434910usize),
                (54usize, 268435454usize),
                (39usize, 268434910usize),
                (52usize, 268435454usize),
                (53usize, 268435454usize),
                (54usize, 268434910usize),
                (44usize, 268435454usize),
                (45usize, 268435454usize),
                (46usize, 268434910usize),
                (47usize, 268434910usize),
                (48usize, 268435454usize),
                (49usize, 268435454usize),
                (50usize, 268434910usize),
                (51usize, 268434910usize),
                (46usize, 268435454usize),
                (47usize, 268435454usize),
                (48usize, 268434910usize),
                (49usize, 268434910usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(117usize, 1744830467usize)];
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
                (2usize, 4usize),
                (3usize, 4usize),
                (4usize, 4usize),
                (5usize, 4usize),
                (6usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 20usize] = [
                (42usize, 268435454usize),
                (43usize, 268435454usize),
                (44usize, 268434910usize),
                (45usize, 268434910usize),
                (40usize, 268435454usize),
                (41usize, 268435454usize),
                (42usize, 268434910usize),
                (43usize, 268434910usize),
                (48usize, 268435454usize),
                (49usize, 268435454usize),
                (50usize, 268434910usize),
                (51usize, 268434910usize),
                (39usize, 268434910usize),
                (52usize, 268435454usize),
                (53usize, 268435454usize),
                (54usize, 268434910usize),
                (50usize, 268435454usize),
                (51usize, 268435454usize),
                (52usize, 268434910usize),
                (53usize, 268434910usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(118usize, 1744830467usize)];
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
                (2usize, 4usize),
                (3usize, 4usize),
                (4usize, 4usize),
                (5usize, 4usize),
                (6usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 20usize] = [
                (46usize, 268435454usize),
                (47usize, 268435454usize),
                (48usize, 268434910usize),
                (49usize, 268434910usize),
                (44usize, 268435454usize),
                (45usize, 268435454usize),
                (46usize, 268434910usize),
                (47usize, 268434910usize),
                (39usize, 268434910usize),
                (52usize, 268435454usize),
                (53usize, 268435454usize),
                (54usize, 268434910usize),
                (40usize, 268435454usize),
                (41usize, 268435454usize),
                (42usize, 268434910usize),
                (43usize, 268434910usize),
                (39usize, 268435454usize),
                (40usize, 268434910usize),
                (41usize, 268434910usize),
                (54usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(119usize, 1744830467usize)];
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
                (2usize, 4usize),
                (3usize, 4usize),
                (4usize, 4usize),
                (5usize, 4usize),
                (6usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 20usize] = [
                (50usize, 268435454usize),
                (51usize, 268435454usize),
                (52usize, 268434910usize),
                (53usize, 268434910usize),
                (48usize, 268435454usize),
                (49usize, 268435454usize),
                (50usize, 268434910usize),
                (51usize, 268434910usize),
                (40usize, 268435454usize),
                (41usize, 268435454usize),
                (42usize, 268434910usize),
                (43usize, 268434910usize),
                (44usize, 268435454usize),
                (45usize, 268435454usize),
                (46usize, 268434910usize),
                (47usize, 268434910usize),
                (42usize, 268435454usize),
                (43usize, 268435454usize),
                (44usize, 268434910usize),
                (45usize, 268434910usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(120usize, 1744830467usize)];
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
                (2usize, 4usize),
                (3usize, 4usize),
                (4usize, 4usize),
                (5usize, 4usize),
                (6usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 18usize] = [
                (60usize, 268435454usize),
                (61usize, 268435454usize),
                (62usize, 268434910usize),
                (63usize, 268434910usize),
                (60usize, 268435454usize),
                (61usize, 268435454usize),
                (62usize, 268434910usize),
                (63usize, 268434910usize),
                (55usize, 268434910usize),
                (68usize, 268435454usize),
                (69usize, 268435454usize),
                (70usize, 268434910usize),
                (66usize, 268435454usize),
                (67usize, 268435454usize),
                (68usize, 268434910usize),
                (69usize, 268434910usize),
                (55usize, 268434910usize),
                (69usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(121usize, 1744830467usize)];
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
                (2usize, 4usize),
                (3usize, 4usize),
                (4usize, 4usize),
                (5usize, 4usize),
                (6usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 18usize] = [
                (64usize, 268435454usize),
                (65usize, 268435454usize),
                (66usize, 268434910usize),
                (67usize, 268434910usize),
                (64usize, 268435454usize),
                (65usize, 268435454usize),
                (66usize, 268434910usize),
                (67usize, 268434910usize),
                (56usize, 268435454usize),
                (57usize, 268435454usize),
                (58usize, 268434910usize),
                (59usize, 268434910usize),
                (55usize, 268435454usize),
                (56usize, 268434910usize),
                (57usize, 268434910usize),
                (70usize, 268435454usize),
                (57usize, 268435454usize),
                (59usize, 268434910usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(122usize, 1744830467usize)];
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
                (2usize, 4usize),
                (3usize, 4usize),
                (4usize, 4usize),
                (5usize, 4usize),
                (6usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 18usize] = [
                (55usize, 268434910usize),
                (68usize, 268435454usize),
                (69usize, 268435454usize),
                (70usize, 268434910usize),
                (55usize, 268434910usize),
                (68usize, 268435454usize),
                (69usize, 268435454usize),
                (70usize, 268434910usize),
                (60usize, 268435454usize),
                (61usize, 268435454usize),
                (62usize, 268434910usize),
                (63usize, 268434910usize),
                (58usize, 268435454usize),
                (59usize, 268435454usize),
                (60usize, 268434910usize),
                (61usize, 268434910usize),
                (61usize, 268435454usize),
                (63usize, 268434910usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(123usize, 1744830467usize)];
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
                (2usize, 4usize),
                (3usize, 4usize),
                (4usize, 4usize),
                (5usize, 4usize),
                (6usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 18usize] = [
                (56usize, 268435454usize),
                (57usize, 268435454usize),
                (58usize, 268434910usize),
                (59usize, 268434910usize),
                (56usize, 268435454usize),
                (57usize, 268435454usize),
                (58usize, 268434910usize),
                (59usize, 268434910usize),
                (64usize, 268435454usize),
                (65usize, 268435454usize),
                (66usize, 268434910usize),
                (67usize, 268434910usize),
                (62usize, 268435454usize),
                (63usize, 268435454usize),
                (64usize, 268434910usize),
                (65usize, 268434910usize),
                (65usize, 268435454usize),
                (67usize, 268434910usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(124usize, 1744830467usize)];
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
                (2usize, 4usize),
                (3usize, 4usize),
                (4usize, 4usize),
                (5usize, 2usize),
                (6usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 18usize] = [
                (83usize, 268435454usize),
                (84usize, 268435454usize),
                (85usize, 268434910usize),
                (86usize, 268434910usize),
                (72usize, 268435454usize),
                (73usize, 268434910usize),
                (74usize, 268434910usize),
                (87usize, 268435454usize),
                (73usize, 268435454usize),
                (74usize, 268435454usize),
                (75usize, 268434910usize),
                (76usize, 268434910usize),
                (74usize, 268435454usize),
                (76usize, 268434910usize),
                (72usize, 268434910usize),
                (85usize, 268435454usize),
                (86usize, 268435454usize),
                (87usize, 268434910usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(125usize, 1744830467usize)];
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
                (2usize, 4usize),
                (3usize, 4usize),
                (4usize, 4usize),
                (5usize, 2usize),
                (6usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 18usize] = [
                (72usize, 268435454usize),
                (73usize, 268434910usize),
                (74usize, 268434910usize),
                (87usize, 268435454usize),
                (75usize, 268435454usize),
                (76usize, 268435454usize),
                (77usize, 268434910usize),
                (78usize, 268434910usize),
                (77usize, 268435454usize),
                (78usize, 268435454usize),
                (79usize, 268434910usize),
                (80usize, 268434910usize),
                (78usize, 268435454usize),
                (80usize, 268434910usize),
                (73usize, 268435454usize),
                (74usize, 268435454usize),
                (75usize, 268434910usize),
                (76usize, 268434910usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(126usize, 1744830467usize)];
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
                (2usize, 4usize),
                (3usize, 4usize),
                (4usize, 4usize),
                (5usize, 2usize),
                (6usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 18usize] = [
                (75usize, 268435454usize),
                (76usize, 268435454usize),
                (77usize, 268434910usize),
                (78usize, 268434910usize),
                (79usize, 268435454usize),
                (80usize, 268435454usize),
                (81usize, 268434910usize),
                (82usize, 268434910usize),
                (81usize, 268435454usize),
                (82usize, 268435454usize),
                (83usize, 268434910usize),
                (84usize, 268434910usize),
                (82usize, 268435454usize),
                (84usize, 268434910usize),
                (77usize, 268435454usize),
                (78usize, 268435454usize),
                (79usize, 268434910usize),
                (80usize, 268434910usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(128usize, 1744830467usize)];
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
                (2usize, 4usize),
                (3usize, 4usize),
                (4usize, 4usize),
                (5usize, 2usize),
                (6usize, 4usize),
            ];
            const VAL_QI: [(usize, usize); 18usize] = [
                (79usize, 268435454usize),
                (80usize, 268435454usize),
                (81usize, 268434910usize),
                (82usize, 268434910usize),
                (83usize, 268435454usize),
                (84usize, 268435454usize),
                (85usize, 268434910usize),
                (86usize, 268434910usize),
                (72usize, 268434910usize),
                (85usize, 268435454usize),
                (86usize, 268435454usize),
                (87usize, 268434910usize),
                (72usize, 268434910usize),
                (86usize, 268435454usize),
                (81usize, 268435454usize),
                (82usize, 268435454usize),
                (83usize, 268434910usize),
                (84usize, 268434910usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(129usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(88usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(88usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(88usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(89usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(89usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(89usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(90usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(90usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(90usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(91usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(91usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(91usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(92usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(92usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(92usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(93usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(93usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(93usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(94usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(94usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(94usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(95usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(95usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(95usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(96usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(96usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(96usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(97usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(97usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(97usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(98usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(98usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(98usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(99usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(99usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(99usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(100usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(100usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(100usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(101usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(101usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(101usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(102usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(102usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(102usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(103usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(103usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(103usize, 1744830467usize)];
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
    output_claims: &[BabyBearExt4; 61usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 37usize] = [
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
        (1usize, 59usize, 0usize),
        (1usize, 60usize, 0usize),
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
    inits_and_teardowns_top_bits: &[u32],
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 37usize] = [
            (SimpleGateType::Copy, [0usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [1usize, 3usize, 0usize, 0usize]),
            (SimpleGateType::Product, [5usize, 7usize, 0usize, 0usize]),
            (SimpleGateType::Product, [9usize, 11usize, 0usize, 0usize]),
            (SimpleGateType::Product, [13usize, 15usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [17usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [2usize, 4usize, 0usize, 0usize]),
            (SimpleGateType::Product, [6usize, 8usize, 0usize, 0usize]),
            (SimpleGateType::Product, [10usize, 12usize, 0usize, 0usize]),
            (SimpleGateType::Product, [14usize, 16usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [18usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupUnbalanced,
                [53usize, 54usize, 55usize, 0usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [51usize, 52usize, 49usize, 50usize],
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
                SimpleGateType::LookupUnbalanced,
                [112usize, 113usize, 114usize, 0usize],
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
            (
                SimpleGateType::LookupAggregatePair,
                [98usize, 99usize, 96usize, 97usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [94usize, 95usize, 92usize, 93usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [90usize, 91usize, 88usize, 89usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [86usize, 87usize, 84usize, 85usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [82usize, 83usize, 80usize, 81usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [78usize, 79usize, 76usize, 77usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [74usize, 75usize, 72usize, 73usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [70usize, 71usize, 68usize, 69usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [66usize, 67usize, 64usize, 65usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [62usize, 63usize, 60usize, 61usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [58usize, 59usize, 56usize, 57usize],
            ),
            (SimpleGateType::Copy, [19usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [20usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 37usize {
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
unsafe fn layer_2_compute_claim(
    output_claims: &[BabyBearExt4; 35usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 24usize] = [
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
        (1usize, 15usize, 0usize),
        (1usize, 16usize, 0usize),
        (2usize, 17usize, 18usize),
        (2usize, 19usize, 20usize),
        (2usize, 21usize, 22usize),
        (2usize, 23usize, 24usize),
        (2usize, 25usize, 26usize),
        (2usize, 27usize, 28usize),
        (2usize, 29usize, 30usize),
        (1usize, 31usize, 0usize),
        (1usize, 32usize, 0usize),
        (1usize, 33usize, 0usize),
        (1usize, 34usize, 0usize),
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
    inits_and_teardowns_top_bits: &[u32],
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 24usize] = [
            (SimpleGateType::Copy, [0usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [1usize, 2usize, 0usize, 0usize]),
            (SimpleGateType::Product, [3usize, 4usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [5usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [6usize, 7usize, 0usize, 0usize]),
            (SimpleGateType::Product, [8usize, 9usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [10usize, 0usize, 0usize, 0usize]),
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
            (
                SimpleGateType::LookupAggregatePair,
                [37usize, 38usize, 35usize, 36usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [33usize, 34usize, 31usize, 32usize],
            ),
            (SimpleGateType::Copy, [29usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [30usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [59usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [60usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 24usize {
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
    output_claims: &[BabyBearExt4; 21usize],
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
        (1usize, 9usize, 0usize),
        (1usize, 10usize, 0usize),
        (2usize, 11usize, 12usize),
        (2usize, 13usize, 14usize),
        (2usize, 15usize, 16usize),
        (2usize, 17usize, 18usize),
        (1usize, 19usize, 0usize),
        (1usize, 20usize, 0usize),
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
    inits_and_teardowns_top_bits: &[u32],
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 15usize] = [
            (SimpleGateType::Copy, [0usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [1usize, 2usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [3usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [4usize, 5usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [6usize, 0usize, 0usize, 0usize]),
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
                [19usize, 20usize, 17usize, 18usize],
            ),
            (SimpleGateType::Copy, [33usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [34usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 15usize {
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
    output_claims: &[BabyBearExt4; 13usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 10usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (1usize, 2usize, 0usize),
        (2usize, 3usize, 4usize),
        (1usize, 5usize, 0usize),
        (1usize, 6usize, 0usize),
        (2usize, 7usize, 8usize),
        (2usize, 9usize, 10usize),
        (1usize, 11usize, 0usize),
        (1usize, 12usize, 0usize),
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
    inits_and_teardowns_top_bits: &[u32],
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
                [9usize, 10usize, 7usize, 8usize],
            ),
            (SimpleGateType::Copy, [5usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [6usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupAggregatePair,
                [17usize, 18usize, 15usize, 16usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [13usize, 14usize, 11usize, 12usize],
            ),
            (SimpleGateType::Copy, [19usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [20usize, 0usize, 0usize, 0usize]),
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
    const DESCS: [(usize, usize, usize); 6usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (2usize, 2usize, 3usize),
        (2usize, 4usize, 5usize),
        (1usize, 6usize, 0usize),
        (1usize, 7usize, 0usize),
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
    inits_and_teardowns_top_bits: &[u32],
) -> [BabyBearExt4; 2] {
    let mut acc = [BabyBearExt4::ZERO; 2];
    let mut current_batch = BabyBearExt4::ONE;
    {
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 6usize] = [
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
            (SimpleGateType::Copy, [11usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [12usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 6usize {
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
            let mut t = *pt.get_unchecked(k);
            field_ops::mul_assign_by_base(&mut t, &prefactor);
            field_ops::add_assign(&mut result, &t);
            field_ops::double(&mut prefactor);
            k += 1;
        }
        while k < 22usize {
            let mut t: BabyBearExt4 = BabyBearExt4::ONE;
            let p = pt.get_unchecked(k);
            field_ops::sub_assign(&mut t, &*p);
            field_ops::mul_assign(&mut result, &t);
            k += 1;
        }
        if result != *state.prev_claims.get_unchecked(277usize) {
            return Err(E::gkr_virtual_setup_eval_mismatch(277usize));
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
            let mut t = *pt.get_unchecked(k);
            field_ops::mul_assign_by_base(&mut t, &prefactor);
            field_ops::add_assign(&mut result, &t);
            field_ops::double(&mut prefactor);
            k += 1;
        }
        while k < 22usize {
            let mut t: BabyBearExt4 = BabyBearExt4::ONE;
            let p = pt.get_unchecked(k);
            field_ops::sub_assign(&mut t, &*p);
            field_ops::mul_assign(&mut result, &t);
            k += 1;
        }
        if result != *state.prev_claims.get_unchecked(278usize) {
            return Err(E::gkr_virtual_setup_eval_mismatch(278usize));
        }
    }
    Ok(())
}
#[allow(unused_variables, unused_mut, unused_unsafe)]
pub(crate) fn verify_gkr<I: NonDeterminismSource<BabyBearField>, E: ErrorCreator>(
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
                evals_commit_buf
                    .data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
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
            0usize, 1usize, 6usize, 7usize, 2usize, 3usize, 4usize, 5usize,
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
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
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
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
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
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
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
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
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
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
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
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
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
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
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
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
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
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
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
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
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
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
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
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
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
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
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
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
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
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
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
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
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
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
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
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
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
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
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
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
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
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
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
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
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
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
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
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
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
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
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
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
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
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
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
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
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
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
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
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
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
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
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
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
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
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
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
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
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
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
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
            {
                let mut i = fc_len;
                while i > 0 {
                    *state.prev_point.get_unchecked_mut(i) = *state.prev_point.get_unchecked(i - 1);
                    i -= 1;
                }
                *state.prev_point.get_unchecked_mut(0) = r_last;
            }
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
            const NUM_AT_POINT_EVALS: usize = 13usize;
            let data_words = NUM_AT_POINT_EVALS * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(NUM_AT_POINT_EVALS);
                let f = layer_5_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                    &initial_transcript.inits_and_teardowns_top_bits,
                );
                verify_final_step_check::<E>(f[0], final_eq_prefactor, final_claim, 5usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let next_batching = draw_single_field_el(ts);
            fold_standard_claims::<13usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<13usize>(),
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
            const NUM_AT_POINT_EVALS: usize = 21usize;
            let data_words = NUM_AT_POINT_EVALS * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(NUM_AT_POINT_EVALS);
                let f = layer_4_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                    &initial_transcript.inits_and_teardowns_top_bits,
                );
                verify_final_step_check::<E>(f[0], final_eq_prefactor, final_claim, 4usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let next_batching = draw_single_field_el(ts);
            fold_standard_claims::<21usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<21usize>(),
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
            const NUM_AT_POINT_EVALS: usize = 35usize;
            let data_words = NUM_AT_POINT_EVALS * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(NUM_AT_POINT_EVALS);
                let f = layer_3_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                    &initial_transcript.inits_and_teardowns_top_bits,
                );
                verify_final_step_check::<E>(f[0], final_eq_prefactor, final_claim, 3usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let next_batching = draw_single_field_el(ts);
            fold_standard_claims::<35usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<35usize>(),
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
            const NUM_AT_POINT_EVALS: usize = 61usize;
            let data_words = NUM_AT_POINT_EVALS * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(NUM_AT_POINT_EVALS);
                let f = layer_2_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                    &initial_transcript.inits_and_teardowns_top_bits,
                );
                verify_final_step_check::<E>(f[0], final_eq_prefactor, final_claim, 2usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let next_batching = draw_single_field_el(ts);
            fold_standard_claims::<61usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<61usize>(),
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
            const NUM_AT_POINT_EVALS: usize = 115usize;
            let data_words = NUM_AT_POINT_EVALS * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(NUM_AT_POINT_EVALS);
                let f = layer_1_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                    &initial_transcript.inits_and_teardowns_top_bits,
                );
                verify_final_step_check::<E>(f[0], final_eq_prefactor, final_claim, 1usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let next_batching = draw_single_field_el(ts);
            fold_standard_claims::<115usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<115usize>(),
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
            const NUM_AT_POINT_EVALS: usize = 276usize;
            let data_words = NUM_AT_POINT_EVALS * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source).as_u32_raw_repr());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(NUM_AT_POINT_EVALS);
                let f = layer_0_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                    &initial_transcript.inits_and_teardowns_top_bits,
                );
                verify_final_step_check::<E>(f[0], final_eq_prefactor, final_claim, 0usize)?;
            }
            const NUM_EXTRA_EVALS: usize = 128usize;
            {
                let mut i = 0;
                while i < NUM_EXTRA_EVALS * EXT_DEGREE {
                    eval_buf.data_write(
                        data_words + i,
                        read_reduced_field_el::<I>(nd_source).as_u32_raw_repr(),
                    );
                    i += 1;
                }
            }
            let mut extra_evals = LazyVec::<BabyBearExt4, NUM_EXTRA_EVALS>::new();
            {
                let slice: &[BabyBearExt4] =
                    unsafe { eval_buf.data_as(NUM_AT_POINT_EVALS + NUM_EXTRA_EVALS) };
                let mut k = NUM_AT_POINT_EVALS;
                while k < NUM_AT_POINT_EVALS + NUM_EXTRA_EVALS {
                    extra_evals.push(unsafe { *slice.get_unchecked(k) });
                    k += 1;
                }
            }
            ts.commit(&mut eval_buf, data_words + NUM_EXTRA_EVALS * EXT_DEGREE);
            let next_batching = draw_single_field_el(ts);
            let final_step_evals: &[[BabyBearExt4; 1]] =
                unsafe { eval_buf.data_as(NUM_AT_POINT_EVALS) };
            state.prev_claims.clear();
            {
                const LAYOUT_KIND: [usize; 404usize] = [
                    1usize, 1usize, 1usize, 0usize, 1usize, 0usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 1usize, 1usize, 1usize,
                    1usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize,
                    1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize,
                    0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 1usize,
                    1usize, 1usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 1usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize,
                    0usize, 0usize, 1usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 1usize,
                    1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 1usize,
                    1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 1usize,
                    1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 1usize,
                    1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 1usize,
                    1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize,
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
                    0usize, 0usize, 0usize, 0usize,
                ];
                const LAYOUT_POS: [usize; 404usize] = [
                    57usize, 58usize, 59usize, 107usize, 60usize, 108usize, 61usize, 62usize,
                    63usize, 64usize, 65usize, 66usize, 67usize, 68usize, 69usize, 109usize,
                    110usize, 70usize, 71usize, 72usize, 73usize, 111usize, 112usize, 74usize,
                    75usize, 76usize, 77usize, 78usize, 113usize, 114usize, 79usize, 80usize,
                    81usize, 82usize, 115usize, 116usize, 83usize, 84usize, 85usize, 86usize,
                    87usize, 117usize, 118usize, 88usize, 89usize, 90usize, 91usize, 119usize,
                    120usize, 92usize, 93usize, 94usize, 95usize, 96usize, 121usize, 122usize,
                    97usize, 98usize, 99usize, 100usize, 123usize, 124usize, 101usize, 102usize,
                    103usize, 104usize, 105usize, 125usize, 126usize, 106usize, 107usize, 108usize,
                    127usize, 128usize, 129usize, 109usize, 110usize, 130usize, 131usize, 111usize,
                    132usize, 133usize, 112usize, 113usize, 134usize, 135usize, 136usize, 137usize,
                    114usize, 115usize, 138usize, 139usize, 116usize, 140usize, 141usize, 117usize,
                    118usize, 142usize, 143usize, 144usize, 145usize, 146usize, 147usize, 148usize,
                    0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize,
                    10usize, 11usize, 12usize, 13usize, 14usize, 15usize, 16usize, 17usize,
                    18usize, 19usize, 20usize, 21usize, 22usize, 23usize, 24usize, 25usize,
                    26usize, 27usize, 28usize, 29usize, 30usize, 31usize, 32usize, 33usize,
                    34usize, 35usize, 36usize, 37usize, 0usize, 1usize, 2usize, 3usize, 4usize,
                    5usize, 6usize, 38usize, 39usize, 40usize, 41usize, 7usize, 8usize, 9usize,
                    10usize, 11usize, 12usize, 13usize, 14usize, 15usize, 16usize, 17usize,
                    18usize, 19usize, 20usize, 21usize, 22usize, 42usize, 43usize, 44usize,
                    45usize, 23usize, 24usize, 25usize, 26usize, 27usize, 28usize, 29usize,
                    30usize, 31usize, 32usize, 33usize, 34usize, 35usize, 36usize, 37usize,
                    38usize, 46usize, 47usize, 48usize, 49usize, 39usize, 40usize, 41usize,
                    42usize, 43usize, 44usize, 45usize, 46usize, 47usize, 48usize, 49usize,
                    50usize, 51usize, 52usize, 53usize, 54usize, 50usize, 51usize, 52usize,
                    53usize, 55usize, 56usize, 57usize, 58usize, 59usize, 60usize, 61usize,
                    62usize, 63usize, 64usize, 65usize, 66usize, 67usize, 68usize, 69usize,
                    70usize, 54usize, 55usize, 56usize, 71usize, 72usize, 73usize, 74usize,
                    75usize, 76usize, 77usize, 78usize, 79usize, 80usize, 81usize, 82usize,
                    83usize, 84usize, 85usize, 86usize, 87usize, 88usize, 89usize, 90usize,
                    91usize, 92usize, 93usize, 94usize, 95usize, 96usize, 97usize, 98usize,
                    99usize, 100usize, 101usize, 102usize, 103usize, 104usize, 105usize, 106usize,
                    119usize, 120usize, 121usize, 122usize, 123usize, 124usize, 125usize, 126usize,
                    127usize, 149usize, 150usize, 151usize, 152usize, 153usize, 154usize, 155usize,
                    156usize, 157usize, 158usize, 159usize, 160usize, 161usize, 162usize, 163usize,
                    164usize, 165usize, 166usize, 167usize, 168usize, 169usize, 170usize, 171usize,
                    172usize, 173usize, 174usize, 175usize, 176usize, 177usize, 178usize, 179usize,
                    180usize, 181usize, 182usize, 183usize, 184usize, 185usize, 186usize, 187usize,
                    188usize, 189usize, 190usize, 191usize, 192usize, 193usize, 194usize, 195usize,
                    196usize, 197usize, 198usize, 199usize, 200usize, 201usize, 202usize, 203usize,
                    204usize, 205usize, 206usize, 207usize, 208usize, 209usize, 210usize, 211usize,
                    212usize, 213usize, 214usize, 215usize, 216usize, 217usize, 218usize, 219usize,
                    220usize, 221usize, 222usize, 223usize, 224usize, 225usize, 226usize, 227usize,
                    228usize, 229usize, 230usize, 231usize, 232usize, 233usize, 234usize, 235usize,
                    236usize, 237usize, 238usize, 239usize, 240usize, 241usize, 242usize, 243usize,
                    244usize, 245usize, 246usize, 247usize, 248usize, 249usize, 250usize, 251usize,
                    252usize, 253usize, 254usize, 255usize, 256usize, 257usize, 258usize, 259usize,
                    260usize, 261usize, 262usize, 263usize, 264usize, 265usize, 266usize, 267usize,
                    268usize, 269usize, 270usize, 271usize, 272usize, 273usize, 274usize, 275usize,
                ];
                let mut i = 0usize;
                while i < 404usize {
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
                const SC_DESCS: [(usize, u32, usize, usize); 33usize] = [
                    (313usize, 0u32, 0usize, 1usize),
                    (314usize, 1476395013u32, 1usize, 3usize),
                    (315usize, 133099247u32, 4usize, 3usize),
                    (316usize, 1476395013u32, 7usize, 3usize),
                    (317usize, 133099247u32, 10usize, 3usize),
                    (318usize, 1476395013u32, 13usize, 3usize),
                    (319usize, 133099247u32, 16usize, 3usize),
                    (320usize, 1476395013u32, 19usize, 3usize),
                    (321usize, 133099247u32, 22usize, 3usize),
                    (322usize, 1476395013u32, 25usize, 3usize),
                    (323usize, 133099247u32, 28usize, 3usize),
                    (324usize, 1476395013u32, 31usize, 3usize),
                    (325usize, 133099247u32, 34usize, 3usize),
                    (326usize, 1476395013u32, 37usize, 3usize),
                    (327usize, 133099247u32, 40usize, 3usize),
                    (328usize, 1476395013u32, 43usize, 3usize),
                    (329usize, 133099247u32, 46usize, 3usize),
                    (330usize, 1476395013u32, 49usize, 3usize),
                    (331usize, 133099247u32, 52usize, 3usize),
                    (332usize, 1476395013u32, 55usize, 3usize),
                    (333usize, 133099247u32, 58usize, 3usize),
                    (334usize, 1476395013u32, 61usize, 3usize),
                    (335usize, 133099247u32, 64usize, 3usize),
                    (336usize, 1476395013u32, 67usize, 3usize),
                    (337usize, 133099247u32, 70usize, 3usize),
                    (338usize, 1476395013u32, 73usize, 3usize),
                    (339usize, 133099247u32, 76usize, 3usize),
                    (340usize, 1476395013u32, 79usize, 3usize),
                    (341usize, 133099247u32, 82usize, 3usize),
                    (342usize, 1476395013u32, 85usize, 3usize),
                    (343usize, 133099247u32, 88usize, 3usize),
                    (344usize, 1476395013u32, 91usize, 3usize),
                    (345usize, 133099247u32, 94usize, 3usize),
                ];
                const SC_TERMS: [(u32, usize); 97usize] = [
                    (16777216u32, 8usize),
                    (1744830467u32, 102usize),
                    (268435454u32, 0usize),
                    (133099247u32, 249usize),
                    (1744830467u32, 103usize),
                    (268435454u32, 1usize),
                    (1744830467u32, 249usize),
                    (1744830467u32, 102usize),
                    (268435454u32, 6usize),
                    (133099247u32, 250usize),
                    (1744830467u32, 103usize),
                    (268435454u32, 7usize),
                    (1744830467u32, 250usize),
                    (1744830467u32, 102usize),
                    (268435454u32, 10usize),
                    (133099247u32, 251usize),
                    (1744830467u32, 103usize),
                    (268435454u32, 11usize),
                    (1744830467u32, 251usize),
                    (1744830467u32, 102usize),
                    (268435454u32, 17usize),
                    (133099247u32, 252usize),
                    (1744830467u32, 103usize),
                    (268435454u32, 18usize),
                    (1744830467u32, 252usize),
                    (1744830467u32, 102usize),
                    (268435454u32, 23usize),
                    (133099247u32, 253usize),
                    (1744830467u32, 103usize),
                    (268435454u32, 24usize),
                    (1744830467u32, 253usize),
                    (1744830467u32, 102usize),
                    (268435454u32, 30usize),
                    (133099247u32, 254usize),
                    (1744830467u32, 103usize),
                    (268435454u32, 31usize),
                    (1744830467u32, 254usize),
                    (1744830467u32, 102usize),
                    (268435454u32, 36usize),
                    (133099247u32, 255usize),
                    (1744830467u32, 103usize),
                    (268435454u32, 37usize),
                    (1744830467u32, 255usize),
                    (1744830467u32, 102usize),
                    (268435454u32, 43usize),
                    (133099247u32, 256usize),
                    (1744830467u32, 103usize),
                    (268435454u32, 44usize),
                    (1744830467u32, 256usize),
                    (1744830467u32, 102usize),
                    (268435454u32, 49usize),
                    (133099247u32, 257usize),
                    (1744830467u32, 103usize),
                    (268435454u32, 50usize),
                    (1744830467u32, 257usize),
                    (1744830467u32, 102usize),
                    (268435454u32, 56usize),
                    (133099247u32, 258usize),
                    (1744830467u32, 103usize),
                    (268435454u32, 57usize),
                    (1744830467u32, 258usize),
                    (1744830467u32, 102usize),
                    (268435454u32, 62usize),
                    (133099247u32, 259usize),
                    (1744830467u32, 103usize),
                    (268435454u32, 63usize),
                    (1744830467u32, 259usize),
                    (1744830467u32, 102usize),
                    (268435454u32, 69usize),
                    (133099247u32, 260usize),
                    (1744830467u32, 103usize),
                    (268435454u32, 70usize),
                    (1744830467u32, 260usize),
                    (1744830467u32, 102usize),
                    (268435454u32, 75usize),
                    (133099247u32, 261usize),
                    (1744830467u32, 103usize),
                    (268435454u32, 76usize),
                    (1744830467u32, 261usize),
                    (1744830467u32, 102usize),
                    (268435454u32, 82usize),
                    (133099247u32, 262usize),
                    (1744830467u32, 103usize),
                    (268435454u32, 83usize),
                    (1744830467u32, 262usize),
                    (1744830467u32, 102usize),
                    (268435454u32, 88usize),
                    (133099247u32, 263usize),
                    (1744830467u32, 103usize),
                    (268435454u32, 89usize),
                    (1744830467u32, 263usize),
                    (1744830467u32, 102usize),
                    (268435454u32, 95usize),
                    (133099247u32, 264usize),
                    (1744830467u32, 103usize),
                    (268435454u32, 96usize),
                    (1744830467u32, 264usize),
                ];
                let mut _sc = 0;
                while _sc < 33usize {
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
                const VL_DESCS: [(usize, usize, usize); 57usize] = [
                    (346usize, 0usize, 9usize),
                    (348usize, 9usize, 9usize),
                    (349usize, 18usize, 9usize),
                    (350usize, 27usize, 9usize),
                    (351usize, 36usize, 9usize),
                    (352usize, 45usize, 9usize),
                    (353usize, 54usize, 9usize),
                    (354usize, 63usize, 9usize),
                    (355usize, 72usize, 9usize),
                    (356usize, 81usize, 9usize),
                    (357usize, 90usize, 9usize),
                    (358usize, 99usize, 9usize),
                    (359usize, 108usize, 9usize),
                    (360usize, 117usize, 9usize),
                    (361usize, 126usize, 9usize),
                    (362usize, 135usize, 9usize),
                    (363usize, 144usize, 9usize),
                    (364usize, 153usize, 9usize),
                    (365usize, 162usize, 9usize),
                    (366usize, 171usize, 9usize),
                    (367usize, 180usize, 9usize),
                    (368usize, 189usize, 9usize),
                    (369usize, 198usize, 9usize),
                    (370usize, 207usize, 9usize),
                    (371usize, 216usize, 9usize),
                    (372usize, 225usize, 9usize),
                    (373usize, 234usize, 9usize),
                    (374usize, 243usize, 9usize),
                    (375usize, 252usize, 9usize),
                    (376usize, 261usize, 9usize),
                    (377usize, 270usize, 9usize),
                    (378usize, 279usize, 9usize),
                    (379usize, 288usize, 9usize),
                    (380usize, 297usize, 9usize),
                    (381usize, 306usize, 9usize),
                    (382usize, 315usize, 9usize),
                    (383usize, 324usize, 9usize),
                    (384usize, 333usize, 9usize),
                    (385usize, 342usize, 9usize),
                    (386usize, 351usize, 9usize),
                    (387usize, 360usize, 9usize),
                    (388usize, 369usize, 9usize),
                    (389usize, 378usize, 9usize),
                    (390usize, 387usize, 9usize),
                    (391usize, 396usize, 9usize),
                    (392usize, 405usize, 9usize),
                    (393usize, 414usize, 9usize),
                    (394usize, 423usize, 9usize),
                    (395usize, 432usize, 9usize),
                    (396usize, 441usize, 9usize),
                    (397usize, 450usize, 9usize),
                    (398usize, 459usize, 9usize),
                    (399usize, 468usize, 9usize),
                    (400usize, 477usize, 9usize),
                    (401usize, 486usize, 9usize),
                    (402usize, 495usize, 9usize),
                    (403usize, 504usize, 9usize),
                ];
                const VL_COLS: [(u32, usize, usize); 513usize] = [
                    (0u32, 0usize, 2usize),
                    (0u32, 2usize, 1usize),
                    (0u32, 3usize, 1usize),
                    (0u32, 4usize, 1usize),
                    (0u32, 5usize, 1usize),
                    (0u32, 6usize, 1usize),
                    (0u32, 7usize, 1usize),
                    (0u32, 8usize, 1usize),
                    (1207959431u32, 9usize, 0usize),
                    (0u32, 9usize, 4usize),
                    (0u32, 13usize, 1usize),
                    (0u32, 14usize, 1usize),
                    (0u32, 15usize, 1usize),
                    (0u32, 16usize, 0usize),
                    (0u32, 16usize, 0usize),
                    (0u32, 16usize, 0usize),
                    (0u32, 16usize, 0usize),
                    (1476394885u32, 16usize, 0usize),
                    (0u32, 16usize, 1usize),
                    (0u32, 17usize, 1usize),
                    (0u32, 18usize, 1usize),
                    (0u32, 19usize, 1usize),
                    (0u32, 20usize, 0usize),
                    (0u32, 20usize, 0usize),
                    (0u32, 20usize, 0usize),
                    (0u32, 20usize, 0usize),
                    (1476394885u32, 20usize, 0usize),
                    (0u32, 20usize, 1usize),
                    (0u32, 21usize, 1usize),
                    (0u32, 22usize, 1usize),
                    (0u32, 23usize, 1usize),
                    (0u32, 24usize, 0usize),
                    (0u32, 24usize, 0usize),
                    (0u32, 24usize, 0usize),
                    (0u32, 24usize, 0usize),
                    (1476394885u32, 24usize, 0usize),
                    (0u32, 24usize, 1usize),
                    (0u32, 25usize, 4usize),
                    (0u32, 29usize, 4usize),
                    (0u32, 33usize, 1usize),
                    (0u32, 34usize, 0usize),
                    (0u32, 34usize, 0usize),
                    (0u32, 34usize, 0usize),
                    (0u32, 34usize, 0usize),
                    (1476394885u32, 34usize, 0usize),
                    (0u32, 34usize, 4usize),
                    (0u32, 38usize, 1usize),
                    (0u32, 39usize, 1usize),
                    (0u32, 40usize, 1usize),
                    (0u32, 41usize, 0usize),
                    (0u32, 41usize, 0usize),
                    (0u32, 41usize, 0usize),
                    (0u32, 41usize, 0usize),
                    (1476394885u32, 41usize, 0usize),
                    (0u32, 41usize, 1usize),
                    (0u32, 42usize, 1usize),
                    (0u32, 43usize, 1usize),
                    (0u32, 44usize, 1usize),
                    (0u32, 45usize, 0usize),
                    (0u32, 45usize, 0usize),
                    (0u32, 45usize, 0usize),
                    (0u32, 45usize, 0usize),
                    (1476394885u32, 45usize, 0usize),
                    (0u32, 45usize, 1usize),
                    (0u32, 46usize, 1usize),
                    (0u32, 47usize, 1usize),
                    (0u32, 48usize, 1usize),
                    (0u32, 49usize, 0usize),
                    (0u32, 49usize, 0usize),
                    (0u32, 49usize, 0usize),
                    (0u32, 49usize, 0usize),
                    (1476394885u32, 49usize, 0usize),
                    (0u32, 49usize, 1usize),
                    (0u32, 50usize, 4usize),
                    (0u32, 54usize, 4usize),
                    (0u32, 58usize, 1usize),
                    (0u32, 59usize, 0usize),
                    (0u32, 59usize, 0usize),
                    (0u32, 59usize, 0usize),
                    (0u32, 59usize, 0usize),
                    (1476394885u32, 59usize, 0usize),
                    (0u32, 59usize, 4usize),
                    (0u32, 63usize, 1usize),
                    (0u32, 64usize, 1usize),
                    (0u32, 65usize, 1usize),
                    (0u32, 66usize, 0usize),
                    (0u32, 66usize, 0usize),
                    (0u32, 66usize, 0usize),
                    (0u32, 66usize, 0usize),
                    (1476394885u32, 66usize, 0usize),
                    (0u32, 66usize, 1usize),
                    (0u32, 67usize, 1usize),
                    (0u32, 68usize, 1usize),
                    (0u32, 69usize, 1usize),
                    (0u32, 70usize, 0usize),
                    (0u32, 70usize, 0usize),
                    (0u32, 70usize, 0usize),
                    (0u32, 70usize, 0usize),
                    (1476394885u32, 70usize, 0usize),
                    (0u32, 70usize, 1usize),
                    (0u32, 71usize, 1usize),
                    (0u32, 72usize, 1usize),
                    (0u32, 73usize, 1usize),
                    (0u32, 74usize, 0usize),
                    (0u32, 74usize, 0usize),
                    (0u32, 74usize, 0usize),
                    (0u32, 74usize, 0usize),
                    (1476394885u32, 74usize, 0usize),
                    (0u32, 74usize, 1usize),
                    (0u32, 75usize, 4usize),
                    (0u32, 79usize, 4usize),
                    (0u32, 83usize, 1usize),
                    (0u32, 84usize, 0usize),
                    (0u32, 84usize, 0usize),
                    (0u32, 84usize, 0usize),
                    (0u32, 84usize, 0usize),
                    (1476394885u32, 84usize, 0usize),
                    (0u32, 84usize, 4usize),
                    (0u32, 88usize, 1usize),
                    (0u32, 89usize, 1usize),
                    (0u32, 90usize, 1usize),
                    (0u32, 91usize, 0usize),
                    (0u32, 91usize, 0usize),
                    (0u32, 91usize, 0usize),
                    (0u32, 91usize, 0usize),
                    (1476394885u32, 91usize, 0usize),
                    (0u32, 91usize, 1usize),
                    (0u32, 92usize, 1usize),
                    (0u32, 93usize, 1usize),
                    (0u32, 94usize, 1usize),
                    (0u32, 95usize, 0usize),
                    (0u32, 95usize, 0usize),
                    (0u32, 95usize, 0usize),
                    (0u32, 95usize, 0usize),
                    (1476394885u32, 95usize, 0usize),
                    (0u32, 95usize, 1usize),
                    (0u32, 96usize, 1usize),
                    (0u32, 97usize, 1usize),
                    (0u32, 98usize, 1usize),
                    (0u32, 99usize, 0usize),
                    (0u32, 99usize, 0usize),
                    (0u32, 99usize, 0usize),
                    (0u32, 99usize, 0usize),
                    (1476394885u32, 99usize, 0usize),
                    (0u32, 99usize, 1usize),
                    (0u32, 100usize, 4usize),
                    (0u32, 104usize, 4usize),
                    (0u32, 108usize, 1usize),
                    (0u32, 109usize, 0usize),
                    (0u32, 109usize, 0usize),
                    (0u32, 109usize, 0usize),
                    (0u32, 109usize, 0usize),
                    (1476394885u32, 109usize, 0usize),
                    (0u32, 109usize, 2usize),
                    (0u32, 111usize, 1usize),
                    (0u32, 112usize, 1usize),
                    (0u32, 113usize, 1usize),
                    (0u32, 114usize, 1usize),
                    (0u32, 115usize, 1usize),
                    (0u32, 116usize, 1usize),
                    (0u32, 117usize, 0usize),
                    (939523977u32, 117usize, 0usize),
                    (0u32, 117usize, 1usize),
                    (0u32, 118usize, 2usize),
                    (0u32, 120usize, 4usize),
                    (0u32, 124usize, 1usize),
                    (0u32, 125usize, 1usize),
                    (0u32, 126usize, 0usize),
                    (0u32, 126usize, 0usize),
                    (0u32, 126usize, 0usize),
                    (671088523u32, 126usize, 0usize),
                    (0u32, 126usize, 2usize),
                    (0u32, 128usize, 2usize),
                    (0u32, 130usize, 4usize),
                    (0u32, 134usize, 1usize),
                    (0u32, 135usize, 1usize),
                    (0u32, 136usize, 0usize),
                    (0u32, 136usize, 0usize),
                    (0u32, 136usize, 0usize),
                    (671088523u32, 136usize, 0usize),
                    (0u32, 136usize, 1usize),
                    (0u32, 137usize, 2usize),
                    (0u32, 139usize, 4usize),
                    (0u32, 143usize, 1usize),
                    (0u32, 144usize, 1usize),
                    (0u32, 145usize, 0usize),
                    (0u32, 145usize, 0usize),
                    (0u32, 145usize, 0usize),
                    (671088523u32, 145usize, 0usize),
                    (0u32, 145usize, 2usize),
                    (0u32, 147usize, 2usize),
                    (0u32, 149usize, 4usize),
                    (0u32, 153usize, 1usize),
                    (0u32, 154usize, 1usize),
                    (0u32, 155usize, 0usize),
                    (0u32, 155usize, 0usize),
                    (0u32, 155usize, 0usize),
                    (671088523u32, 155usize, 0usize),
                    (0u32, 155usize, 1usize),
                    (0u32, 156usize, 2usize),
                    (0u32, 158usize, 4usize),
                    (0u32, 162usize, 1usize),
                    (0u32, 163usize, 1usize),
                    (0u32, 164usize, 0usize),
                    (0u32, 164usize, 0usize),
                    (0u32, 164usize, 0usize),
                    (671088523u32, 164usize, 0usize),
                    (0u32, 164usize, 2usize),
                    (0u32, 166usize, 2usize),
                    (0u32, 168usize, 4usize),
                    (0u32, 172usize, 1usize),
                    (0u32, 173usize, 1usize),
                    (0u32, 174usize, 0usize),
                    (0u32, 174usize, 0usize),
                    (0u32, 174usize, 0usize),
                    (671088523u32, 174usize, 0usize),
                    (0u32, 174usize, 1usize),
                    (0u32, 175usize, 2usize),
                    (0u32, 177usize, 4usize),
                    (0u32, 181usize, 1usize),
                    (0u32, 182usize, 1usize),
                    (0u32, 183usize, 0usize),
                    (0u32, 183usize, 0usize),
                    (0u32, 183usize, 0usize),
                    (671088523u32, 183usize, 0usize),
                    (0u32, 183usize, 2usize),
                    (0u32, 185usize, 2usize),
                    (0u32, 187usize, 4usize),
                    (0u32, 191usize, 1usize),
                    (0u32, 192usize, 1usize),
                    (0u32, 193usize, 0usize),
                    (0u32, 193usize, 0usize),
                    (0u32, 193usize, 0usize),
                    (671088523u32, 193usize, 0usize),
                    (0u32, 193usize, 1usize),
                    (0u32, 194usize, 2usize),
                    (0u32, 196usize, 5usize),
                    (0u32, 201usize, 1usize),
                    (0u32, 202usize, 1usize),
                    (0u32, 203usize, 0usize),
                    (0u32, 203usize, 0usize),
                    (0u32, 203usize, 0usize),
                    (671088523u32, 203usize, 0usize),
                    (0u32, 203usize, 2usize),
                    (0u32, 205usize, 2usize),
                    (0u32, 207usize, 5usize),
                    (0u32, 212usize, 1usize),
                    (0u32, 213usize, 1usize),
                    (0u32, 214usize, 0usize),
                    (0u32, 214usize, 0usize),
                    (0u32, 214usize, 0usize),
                    (671088523u32, 214usize, 0usize),
                    (0u32, 214usize, 1usize),
                    (0u32, 215usize, 2usize),
                    (0u32, 217usize, 5usize),
                    (0u32, 222usize, 1usize),
                    (0u32, 223usize, 1usize),
                    (0u32, 224usize, 0usize),
                    (0u32, 224usize, 0usize),
                    (0u32, 224usize, 0usize),
                    (671088523u32, 224usize, 0usize),
                    (0u32, 224usize, 2usize),
                    (0u32, 226usize, 2usize),
                    (0u32, 228usize, 5usize),
                    (0u32, 233usize, 1usize),
                    (0u32, 234usize, 1usize),
                    (0u32, 235usize, 0usize),
                    (0u32, 235usize, 0usize),
                    (0u32, 235usize, 0usize),
                    (671088523u32, 235usize, 0usize),
                    (0u32, 235usize, 1usize),
                    (0u32, 236usize, 2usize),
                    (0u32, 238usize, 5usize),
                    (0u32, 243usize, 1usize),
                    (0u32, 244usize, 1usize),
                    (0u32, 245usize, 0usize),
                    (0u32, 245usize, 0usize),
                    (0u32, 245usize, 0usize),
                    (671088523u32, 245usize, 0usize),
                    (0u32, 245usize, 2usize),
                    (0u32, 247usize, 2usize),
                    (0u32, 249usize, 5usize),
                    (0u32, 254usize, 1usize),
                    (0u32, 255usize, 1usize),
                    (0u32, 256usize, 0usize),
                    (0u32, 256usize, 0usize),
                    (0u32, 256usize, 0usize),
                    (671088523u32, 256usize, 0usize),
                    (0u32, 256usize, 1usize),
                    (0u32, 257usize, 2usize),
                    (0u32, 259usize, 5usize),
                    (0u32, 264usize, 1usize),
                    (0u32, 265usize, 1usize),
                    (0u32, 266usize, 0usize),
                    (0u32, 266usize, 0usize),
                    (0u32, 266usize, 0usize),
                    (671088523u32, 266usize, 0usize),
                    (0u32, 266usize, 2usize),
                    (0u32, 268usize, 2usize),
                    (0u32, 270usize, 5usize),
                    (0u32, 275usize, 1usize),
                    (0u32, 276usize, 1usize),
                    (0u32, 277usize, 0usize),
                    (0u32, 277usize, 0usize),
                    (0u32, 277usize, 0usize),
                    (671088523u32, 277usize, 0usize),
                    (0u32, 277usize, 1usize),
                    (0u32, 278usize, 2usize),
                    (0u32, 280usize, 5usize),
                    (0u32, 285usize, 1usize),
                    (0u32, 286usize, 1usize),
                    (0u32, 287usize, 0usize),
                    (0u32, 287usize, 0usize),
                    (0u32, 287usize, 0usize),
                    (671088523u32, 287usize, 0usize),
                    (0u32, 287usize, 2usize),
                    (0u32, 289usize, 2usize),
                    (0u32, 291usize, 5usize),
                    (0u32, 296usize, 1usize),
                    (0u32, 297usize, 1usize),
                    (0u32, 298usize, 0usize),
                    (0u32, 298usize, 0usize),
                    (0u32, 298usize, 0usize),
                    (671088523u32, 298usize, 0usize),
                    (0u32, 298usize, 1usize),
                    (0u32, 299usize, 2usize),
                    (0u32, 301usize, 5usize),
                    (0u32, 306usize, 1usize),
                    (0u32, 307usize, 1usize),
                    (0u32, 308usize, 0usize),
                    (0u32, 308usize, 0usize),
                    (0u32, 308usize, 0usize),
                    (671088523u32, 308usize, 0usize),
                    (0u32, 308usize, 2usize),
                    (0u32, 310usize, 2usize),
                    (0u32, 312usize, 5usize),
                    (0u32, 317usize, 1usize),
                    (0u32, 318usize, 1usize),
                    (0u32, 319usize, 0usize),
                    (0u32, 319usize, 0usize),
                    (0u32, 319usize, 0usize),
                    (671088523u32, 319usize, 0usize),
                    (0u32, 319usize, 1usize),
                    (0u32, 320usize, 2usize),
                    (0u32, 322usize, 5usize),
                    (0u32, 327usize, 1usize),
                    (0u32, 328usize, 1usize),
                    (0u32, 329usize, 0usize),
                    (0u32, 329usize, 0usize),
                    (0u32, 329usize, 0usize),
                    (671088523u32, 329usize, 0usize),
                    (0u32, 329usize, 2usize),
                    (0u32, 331usize, 2usize),
                    (0u32, 333usize, 5usize),
                    (0u32, 338usize, 1usize),
                    (0u32, 339usize, 1usize),
                    (0u32, 340usize, 0usize),
                    (0u32, 340usize, 0usize),
                    (0u32, 340usize, 0usize),
                    (671088523u32, 340usize, 0usize),
                    (0u32, 340usize, 1usize),
                    (0u32, 341usize, 2usize),
                    (0u32, 343usize, 5usize),
                    (0u32, 348usize, 1usize),
                    (0u32, 349usize, 1usize),
                    (0u32, 350usize, 0usize),
                    (0u32, 350usize, 0usize),
                    (0u32, 350usize, 0usize),
                    (671088523u32, 350usize, 0usize),
                    (0u32, 350usize, 2usize),
                    (0u32, 352usize, 2usize),
                    (0u32, 354usize, 5usize),
                    (0u32, 359usize, 1usize),
                    (0u32, 360usize, 1usize),
                    (0u32, 361usize, 0usize),
                    (0u32, 361usize, 0usize),
                    (0u32, 361usize, 0usize),
                    (671088523u32, 361usize, 0usize),
                    (0u32, 361usize, 1usize),
                    (0u32, 362usize, 2usize),
                    (0u32, 364usize, 4usize),
                    (0u32, 368usize, 1usize),
                    (0u32, 369usize, 1usize),
                    (0u32, 370usize, 0usize),
                    (0u32, 370usize, 0usize),
                    (0u32, 370usize, 0usize),
                    (671088523u32, 370usize, 0usize),
                    (0u32, 370usize, 2usize),
                    (0u32, 372usize, 2usize),
                    (0u32, 374usize, 4usize),
                    (0u32, 378usize, 1usize),
                    (0u32, 379usize, 1usize),
                    (0u32, 380usize, 0usize),
                    (0u32, 380usize, 0usize),
                    (0u32, 380usize, 0usize),
                    (671088523u32, 380usize, 0usize),
                    (0u32, 380usize, 1usize),
                    (0u32, 381usize, 2usize),
                    (0u32, 383usize, 4usize),
                    (0u32, 387usize, 1usize),
                    (0u32, 388usize, 1usize),
                    (0u32, 389usize, 0usize),
                    (0u32, 389usize, 0usize),
                    (0u32, 389usize, 0usize),
                    (671088523u32, 389usize, 0usize),
                    (0u32, 389usize, 2usize),
                    (0u32, 391usize, 2usize),
                    (0u32, 393usize, 4usize),
                    (0u32, 397usize, 1usize),
                    (0u32, 398usize, 1usize),
                    (0u32, 399usize, 0usize),
                    (0u32, 399usize, 0usize),
                    (0u32, 399usize, 0usize),
                    (671088523u32, 399usize, 0usize),
                    (0u32, 399usize, 1usize),
                    (0u32, 400usize, 2usize),
                    (0u32, 402usize, 4usize),
                    (0u32, 406usize, 1usize),
                    (0u32, 407usize, 1usize),
                    (0u32, 408usize, 0usize),
                    (0u32, 408usize, 0usize),
                    (0u32, 408usize, 0usize),
                    (671088523u32, 408usize, 0usize),
                    (0u32, 408usize, 2usize),
                    (0u32, 410usize, 2usize),
                    (0u32, 412usize, 4usize),
                    (0u32, 416usize, 1usize),
                    (0u32, 417usize, 1usize),
                    (0u32, 418usize, 0usize),
                    (0u32, 418usize, 0usize),
                    (0u32, 418usize, 0usize),
                    (671088523u32, 418usize, 0usize),
                    (0u32, 418usize, 1usize),
                    (0u32, 419usize, 2usize),
                    (0u32, 421usize, 4usize),
                    (0u32, 425usize, 1usize),
                    (0u32, 426usize, 1usize),
                    (0u32, 427usize, 0usize),
                    (0u32, 427usize, 0usize),
                    (0u32, 427usize, 0usize),
                    (671088523u32, 427usize, 0usize),
                    (0u32, 427usize, 2usize),
                    (0u32, 429usize, 2usize),
                    (0u32, 431usize, 4usize),
                    (0u32, 435usize, 1usize),
                    (0u32, 436usize, 1usize),
                    (0u32, 437usize, 0usize),
                    (0u32, 437usize, 0usize),
                    (0u32, 437usize, 0usize),
                    (671088523u32, 437usize, 0usize),
                    (0u32, 437usize, 1usize),
                    (0u32, 438usize, 2usize),
                    (0u32, 440usize, 4usize),
                    (0u32, 444usize, 1usize),
                    (0u32, 445usize, 1usize),
                    (0u32, 446usize, 0usize),
                    (0u32, 446usize, 0usize),
                    (0u32, 446usize, 0usize),
                    (671088523u32, 446usize, 0usize),
                    (0u32, 446usize, 2usize),
                    (0u32, 448usize, 2usize),
                    (0u32, 450usize, 4usize),
                    (0u32, 454usize, 1usize),
                    (0u32, 455usize, 1usize),
                    (0u32, 456usize, 0usize),
                    (0u32, 456usize, 0usize),
                    (0u32, 456usize, 0usize),
                    (671088523u32, 456usize, 0usize),
                    (0u32, 456usize, 1usize),
                    (0u32, 457usize, 2usize),
                    (0u32, 459usize, 4usize),
                    (0u32, 463usize, 1usize),
                    (0u32, 464usize, 1usize),
                    (0u32, 465usize, 0usize),
                    (0u32, 465usize, 0usize),
                    (0u32, 465usize, 0usize),
                    (671088523u32, 465usize, 0usize),
                    (0u32, 465usize, 2usize),
                    (0u32, 467usize, 2usize),
                    (0u32, 469usize, 4usize),
                    (0u32, 473usize, 1usize),
                    (0u32, 474usize, 1usize),
                    (0u32, 475usize, 0usize),
                    (0u32, 475usize, 0usize),
                    (0u32, 475usize, 0usize),
                    (671088523u32, 475usize, 0usize),
                    (0u32, 475usize, 1usize),
                    (0u32, 476usize, 2usize),
                    (0u32, 478usize, 4usize),
                    (0u32, 482usize, 1usize),
                    (0u32, 483usize, 1usize),
                    (0u32, 484usize, 0usize),
                    (0u32, 484usize, 0usize),
                    (0u32, 484usize, 0usize),
                    (671088523u32, 484usize, 0usize),
                    (0u32, 484usize, 2usize),
                    (0u32, 486usize, 2usize),
                    (0u32, 488usize, 4usize),
                    (0u32, 492usize, 1usize),
                    (0u32, 493usize, 1usize),
                    (0u32, 494usize, 0usize),
                    (0u32, 494usize, 0usize),
                    (0u32, 494usize, 0usize),
                    (671088523u32, 494usize, 0usize),
                    (0u32, 494usize, 1usize),
                    (0u32, 495usize, 2usize),
                    (0u32, 497usize, 4usize),
                    (0u32, 501usize, 1usize),
                    (0u32, 502usize, 1usize),
                    (0u32, 503usize, 0usize),
                    (0u32, 503usize, 0usize),
                    (0u32, 503usize, 0usize),
                    (671088523u32, 503usize, 0usize),
                ];
                const VL_TERMS: [(u32, usize); 503usize] = [
                    (134213359u32, 101usize),
                    (268435454u32, 2usize),
                    (268435454u32, 14usize),
                    (268435454u32, 27usize),
                    (268435454u32, 40usize),
                    (268435454u32, 53usize),
                    (268435454u32, 66usize),
                    (268435454u32, 79usize),
                    (268435454u32, 92usize),
                    (1048576u32, 98usize),
                    (2012217345u32, 125usize),
                    (1996488705u32, 126usize),
                    (1744830465u32, 127usize),
                    (268435454u32, 116usize),
                    (268435454u32, 104usize),
                    (268435454u32, 128usize),
                    (268435454u32, 116usize),
                    (268435454u32, 117usize),
                    (268435454u32, 105usize),
                    (268435454u32, 129usize),
                    (268435454u32, 117usize),
                    (268435454u32, 118usize),
                    (268435454u32, 106usize),
                    (268435454u32, 130usize),
                    (268435454u32, 118usize),
                    (1048576u32, 90usize),
                    (2012217345u32, 116usize),
                    (1996488705u32, 117usize),
                    (1744830465u32, 118usize),
                    (1048576u32, 77usize),
                    (2012217345u32, 104usize),
                    (1996488705u32, 105usize),
                    (1744830465u32, 106usize),
                    (268435454u32, 131usize),
                    (1048576u32, 90usize),
                    (2012217345u32, 116usize),
                    (1996488705u32, 117usize),
                    (1744830465u32, 118usize),
                    (268435454u32, 119usize),
                    (268435454u32, 107usize),
                    (268435454u32, 132usize),
                    (268435454u32, 119usize),
                    (268435454u32, 120usize),
                    (268435454u32, 108usize),
                    (268435454u32, 133usize),
                    (268435454u32, 120usize),
                    (268435454u32, 121usize),
                    (268435454u32, 109usize),
                    (268435454u32, 134usize),
                    (268435454u32, 121usize),
                    (1048576u32, 91usize),
                    (2012217345u32, 119usize),
                    (1996488705u32, 120usize),
                    (1744830465u32, 121usize),
                    (1048576u32, 78usize),
                    (2012217345u32, 107usize),
                    (1996488705u32, 108usize),
                    (1744830465u32, 109usize),
                    (268435454u32, 135usize),
                    (1048576u32, 91usize),
                    (2012217345u32, 119usize),
                    (1996488705u32, 120usize),
                    (1744830465u32, 121usize),
                    (268435454u32, 122usize),
                    (268435454u32, 110usize),
                    (268435454u32, 136usize),
                    (268435454u32, 122usize),
                    (268435454u32, 123usize),
                    (268435454u32, 111usize),
                    (268435454u32, 137usize),
                    (268435454u32, 123usize),
                    (268435454u32, 124usize),
                    (268435454u32, 112usize),
                    (268435454u32, 138usize),
                    (268435454u32, 124usize),
                    (1048576u32, 97usize),
                    (2012217345u32, 122usize),
                    (1996488705u32, 123usize),
                    (1744830465u32, 124usize),
                    (1048576u32, 84usize),
                    (2012217345u32, 110usize),
                    (1996488705u32, 111usize),
                    (1744830465u32, 112usize),
                    (268435454u32, 139usize),
                    (1048576u32, 97usize),
                    (2012217345u32, 122usize),
                    (1996488705u32, 123usize),
                    (1744830465u32, 124usize),
                    (268435454u32, 125usize),
                    (268435454u32, 113usize),
                    (268435454u32, 140usize),
                    (268435454u32, 125usize),
                    (268435454u32, 126usize),
                    (268435454u32, 114usize),
                    (268435454u32, 141usize),
                    (268435454u32, 126usize),
                    (268435454u32, 127usize),
                    (268435454u32, 115usize),
                    (268435454u32, 142usize),
                    (268435454u32, 127usize),
                    (1048576u32, 98usize),
                    (2012217345u32, 125usize),
                    (1996488705u32, 126usize),
                    (1744830465u32, 127usize),
                    (1048576u32, 85usize),
                    (2012217345u32, 113usize),
                    (1996488705u32, 114usize),
                    (1744830465u32, 115usize),
                    (268435454u32, 143usize),
                    (134213359u32, 101usize),
                    (268435454u32, 2usize),
                    (268435454u32, 4usize),
                    (268435454u32, 144usize),
                    (268435454u32, 145usize),
                    (268435454u32, 146usize),
                    (268435454u32, 147usize),
                    (268435454u32, 148usize),
                    (268435454u32, 149usize),
                    (268435454u32, 128usize),
                    (268435422u32, 129usize),
                    (268435454u32, 145usize),
                    (1610612724u32, 146usize),
                    (1073741816u32, 147usize),
                    (805306362u32, 148usize),
                    (268435454u32, 153usize),
                    (268435454u32, 154usize),
                    (16777216u32, 12usize),
                    (1996488705u32, 149usize),
                    (268435454u32, 130usize),
                    (268435422u32, 131usize),
                    (268435454u32, 145usize),
                    (1610612724u32, 146usize),
                    (1073741816u32, 147usize),
                    (805306362u32, 148usize),
                    (268435454u32, 155usize),
                    (268435454u32, 156usize),
                    (268435454u32, 150usize),
                    (268435454u32, 132usize),
                    (268435422u32, 133usize),
                    (268435454u32, 145usize),
                    (1610612724u32, 146usize),
                    (1073741816u32, 147usize),
                    (805306362u32, 148usize),
                    (268435454u32, 157usize),
                    (268435454u32, 158usize),
                    (16777216u32, 13usize),
                    (1996488705u32, 150usize),
                    (268435454u32, 134usize),
                    (268435422u32, 135usize),
                    (268435454u32, 145usize),
                    (1610612724u32, 146usize),
                    (1073741816u32, 147usize),
                    (805306362u32, 148usize),
                    (268435454u32, 159usize),
                    (268435454u32, 160usize),
                    (268435454u32, 151usize),
                    (268435454u32, 136usize),
                    (268435422u32, 137usize),
                    (268435454u32, 145usize),
                    (1610612724u32, 146usize),
                    (1073741816u32, 147usize),
                    (805306362u32, 148usize),
                    (268435454u32, 161usize),
                    (268435454u32, 162usize),
                    (16777216u32, 19usize),
                    (1996488705u32, 151usize),
                    (268435454u32, 138usize),
                    (268435422u32, 139usize),
                    (268435454u32, 145usize),
                    (1610612724u32, 146usize),
                    (1073741816u32, 147usize),
                    (805306362u32, 148usize),
                    (268435454u32, 163usize),
                    (268435454u32, 164usize),
                    (268435454u32, 152usize),
                    (268435454u32, 140usize),
                    (268435422u32, 141usize),
                    (268435454u32, 145usize),
                    (1610612724u32, 146usize),
                    (1073741816u32, 147usize),
                    (805306362u32, 148usize),
                    (268435454u32, 165usize),
                    (268435454u32, 166usize),
                    (16777216u32, 20usize),
                    (1996488705u32, 152usize),
                    (268435454u32, 142usize),
                    (268435422u32, 143usize),
                    (268435454u32, 145usize),
                    (1610612724u32, 146usize),
                    (1073741816u32, 147usize),
                    (805306362u32, 148usize),
                    (268435454u32, 167usize),
                    (268435454u32, 168usize),
                    (268435454u32, 169usize),
                    (268435454u32, 128usize),
                    (268435422u32, 129usize),
                    (1073741816u32, 144usize),
                    (1073741816u32, 145usize),
                    (1610612724u32, 146usize),
                    (1879048178u32, 147usize),
                    (1073741816u32, 148usize),
                    (268435454u32, 173usize),
                    (268435454u32, 174usize),
                    (16777216u32, 25usize),
                    (1996488705u32, 169usize),
                    (268435454u32, 130usize),
                    (268435422u32, 131usize),
                    (1073741816u32, 144usize),
                    (1073741816u32, 145usize),
                    (1610612724u32, 146usize),
                    (1879048178u32, 147usize),
                    (1073741816u32, 148usize),
                    (268435454u32, 175usize),
                    (268435454u32, 176usize),
                    (268435454u32, 170usize),
                    (268435454u32, 132usize),
                    (268435422u32, 133usize),
                    (1073741816u32, 144usize),
                    (1073741816u32, 145usize),
                    (1610612724u32, 146usize),
                    (1879048178u32, 147usize),
                    (1073741816u32, 148usize),
                    (268435454u32, 177usize),
                    (268435454u32, 178usize),
                    (16777216u32, 26usize),
                    (1996488705u32, 170usize),
                    (268435454u32, 134usize),
                    (268435422u32, 135usize),
                    (1073741816u32, 144usize),
                    (1073741816u32, 145usize),
                    (1610612724u32, 146usize),
                    (1879048178u32, 147usize),
                    (1073741816u32, 148usize),
                    (268435454u32, 179usize),
                    (268435454u32, 180usize),
                    (268435454u32, 171usize),
                    (268435454u32, 136usize),
                    (268435422u32, 137usize),
                    (1073741816u32, 144usize),
                    (1073741816u32, 145usize),
                    (1610612724u32, 146usize),
                    (1879048178u32, 147usize),
                    (1073741816u32, 148usize),
                    (268435454u32, 181usize),
                    (268435454u32, 182usize),
                    (16777216u32, 32usize),
                    (1996488705u32, 171usize),
                    (268435454u32, 138usize),
                    (268435422u32, 139usize),
                    (1073741816u32, 144usize),
                    (1073741816u32, 145usize),
                    (1610612724u32, 146usize),
                    (1879048178u32, 147usize),
                    (1073741816u32, 148usize),
                    (268435454u32, 183usize),
                    (268435454u32, 184usize),
                    (268435454u32, 172usize),
                    (268435454u32, 140usize),
                    (268435422u32, 141usize),
                    (1073741816u32, 144usize),
                    (1073741816u32, 145usize),
                    (1610612724u32, 146usize),
                    (1879048178u32, 147usize),
                    (1073741816u32, 148usize),
                    (268435454u32, 185usize),
                    (268435454u32, 186usize),
                    (16777216u32, 33usize),
                    (1996488705u32, 172usize),
                    (268435454u32, 142usize),
                    (268435422u32, 143usize),
                    (1073741816u32, 144usize),
                    (1073741816u32, 145usize),
                    (1610612724u32, 146usize),
                    (1879048178u32, 147usize),
                    (1073741816u32, 148usize),
                    (268435454u32, 187usize),
                    (268435454u32, 188usize),
                    (268435454u32, 189usize),
                    (268435454u32, 128usize),
                    (268435422u32, 129usize),
                    (805306362u32, 144usize),
                    (536870908u32, 145usize),
                    (805306362u32, 146usize),
                    (268435454u32, 147usize),
                    (1879048178u32, 148usize),
                    (268435454u32, 193usize),
                    (268435454u32, 194usize),
                    (16777216u32, 38usize),
                    (1996488705u32, 189usize),
                    (268435454u32, 130usize),
                    (268435422u32, 131usize),
                    (805306362u32, 144usize),
                    (536870908u32, 145usize),
                    (805306362u32, 146usize),
                    (268435454u32, 147usize),
                    (1879048178u32, 148usize),
                    (268435454u32, 195usize),
                    (268435454u32, 196usize),
                    (268435454u32, 190usize),
                    (268435454u32, 132usize),
                    (268435422u32, 133usize),
                    (805306362u32, 144usize),
                    (536870908u32, 145usize),
                    (805306362u32, 146usize),
                    (268435454u32, 147usize),
                    (1879048178u32, 148usize),
                    (268435454u32, 197usize),
                    (268435454u32, 198usize),
                    (16777216u32, 39usize),
                    (1996488705u32, 190usize),
                    (268435454u32, 134usize),
                    (268435422u32, 135usize),
                    (805306362u32, 144usize),
                    (536870908u32, 145usize),
                    (805306362u32, 146usize),
                    (268435454u32, 147usize),
                    (1879048178u32, 148usize),
                    (268435454u32, 199usize),
                    (268435454u32, 200usize),
                    (268435454u32, 191usize),
                    (268435454u32, 136usize),
                    (268435422u32, 137usize),
                    (805306362u32, 144usize),
                    (536870908u32, 145usize),
                    (805306362u32, 146usize),
                    (268435454u32, 147usize),
                    (1879048178u32, 148usize),
                    (268435454u32, 201usize),
                    (268435454u32, 202usize),
                    (16777216u32, 45usize),
                    (1996488705u32, 191usize),
                    (268435454u32, 138usize),
                    (268435422u32, 139usize),
                    (805306362u32, 144usize),
                    (536870908u32, 145usize),
                    (805306362u32, 146usize),
                    (268435454u32, 147usize),
                    (1879048178u32, 148usize),
                    (268435454u32, 203usize),
                    (268435454u32, 204usize),
                    (268435454u32, 192usize),
                    (268435454u32, 140usize),
                    (268435422u32, 141usize),
                    (805306362u32, 144usize),
                    (536870908u32, 145usize),
                    (805306362u32, 146usize),
                    (268435454u32, 147usize),
                    (1879048178u32, 148usize),
                    (268435454u32, 205usize),
                    (268435454u32, 206usize),
                    (16777216u32, 46usize),
                    (1996488705u32, 192usize),
                    (268435454u32, 142usize),
                    (268435422u32, 143usize),
                    (805306362u32, 144usize),
                    (536870908u32, 145usize),
                    (805306362u32, 146usize),
                    (268435454u32, 147usize),
                    (1879048178u32, 148usize),
                    (268435454u32, 207usize),
                    (268435454u32, 208usize),
                    (268435454u32, 209usize),
                    (268435454u32, 128usize),
                    (268435422u32, 129usize),
                    (268435454u32, 144usize),
                    (1342177270u32, 145usize),
                    (1879048178u32, 146usize),
                    (1342177270u32, 147usize),
                    (268435454u32, 213usize),
                    (268435454u32, 214usize),
                    (16777216u32, 51usize),
                    (1996488705u32, 209usize),
                    (268435454u32, 130usize),
                    (268435422u32, 131usize),
                    (268435454u32, 144usize),
                    (1342177270u32, 145usize),
                    (1879048178u32, 146usize),
                    (1342177270u32, 147usize),
                    (268435454u32, 215usize),
                    (268435454u32, 216usize),
                    (268435454u32, 210usize),
                    (268435454u32, 132usize),
                    (268435422u32, 133usize),
                    (268435454u32, 144usize),
                    (1342177270u32, 145usize),
                    (1879048178u32, 146usize),
                    (1342177270u32, 147usize),
                    (268435454u32, 217usize),
                    (268435454u32, 218usize),
                    (16777216u32, 52usize),
                    (1996488705u32, 210usize),
                    (268435454u32, 134usize),
                    (268435422u32, 135usize),
                    (268435454u32, 144usize),
                    (1342177270u32, 145usize),
                    (1879048178u32, 146usize),
                    (1342177270u32, 147usize),
                    (268435454u32, 219usize),
                    (268435454u32, 220usize),
                    (268435454u32, 211usize),
                    (268435454u32, 136usize),
                    (268435422u32, 137usize),
                    (268435454u32, 144usize),
                    (1342177270u32, 145usize),
                    (1879048178u32, 146usize),
                    (1342177270u32, 147usize),
                    (268435454u32, 221usize),
                    (268435454u32, 222usize),
                    (16777216u32, 58usize),
                    (1996488705u32, 211usize),
                    (268435454u32, 138usize),
                    (268435422u32, 139usize),
                    (268435454u32, 144usize),
                    (1342177270u32, 145usize),
                    (1879048178u32, 146usize),
                    (1342177270u32, 147usize),
                    (268435454u32, 223usize),
                    (268435454u32, 224usize),
                    (268435454u32, 212usize),
                    (268435454u32, 140usize),
                    (268435422u32, 141usize),
                    (268435454u32, 144usize),
                    (1342177270u32, 145usize),
                    (1879048178u32, 146usize),
                    (1342177270u32, 147usize),
                    (268435454u32, 225usize),
                    (268435454u32, 226usize),
                    (16777216u32, 59usize),
                    (1996488705u32, 212usize),
                    (268435454u32, 142usize),
                    (268435422u32, 143usize),
                    (268435454u32, 144usize),
                    (1342177270u32, 145usize),
                    (1879048178u32, 146usize),
                    (1342177270u32, 147usize),
                    (268435454u32, 227usize),
                    (268435454u32, 228usize),
                    (268435454u32, 229usize),
                    (268435454u32, 128usize),
                    (268435422u32, 129usize),
                    (536870908u32, 144usize),
                    (536870908u32, 145usize),
                    (1342177270u32, 146usize),
                    (1610612724u32, 148usize),
                    (268435454u32, 233usize),
                    (268435454u32, 234usize),
                    (16777216u32, 64usize),
                    (1996488705u32, 229usize),
                    (268435454u32, 130usize),
                    (268435422u32, 131usize),
                    (536870908u32, 144usize),
                    (536870908u32, 145usize),
                    (1342177270u32, 146usize),
                    (1610612724u32, 148usize),
                    (268435454u32, 235usize),
                    (268435454u32, 236usize),
                    (268435454u32, 230usize),
                    (268435454u32, 132usize),
                    (268435422u32, 133usize),
                    (536870908u32, 144usize),
                    (536870908u32, 145usize),
                    (1342177270u32, 146usize),
                    (1610612724u32, 148usize),
                    (268435454u32, 237usize),
                    (268435454u32, 238usize),
                    (16777216u32, 65usize),
                    (1996488705u32, 230usize),
                    (268435454u32, 134usize),
                    (268435422u32, 135usize),
                    (536870908u32, 144usize),
                    (536870908u32, 145usize),
                    (1342177270u32, 146usize),
                    (1610612724u32, 148usize),
                    (268435454u32, 239usize),
                    (268435454u32, 240usize),
                    (268435454u32, 231usize),
                    (268435454u32, 136usize),
                    (268435422u32, 137usize),
                    (536870908u32, 144usize),
                    (536870908u32, 145usize),
                    (1342177270u32, 146usize),
                    (1610612724u32, 148usize),
                    (268435454u32, 241usize),
                    (268435454u32, 242usize),
                    (16777216u32, 71usize),
                    (1996488705u32, 231usize),
                    (268435454u32, 138usize),
                    (268435422u32, 139usize),
                    (536870908u32, 144usize),
                    (536870908u32, 145usize),
                    (1342177270u32, 146usize),
                    (1610612724u32, 148usize),
                    (268435454u32, 243usize),
                    (268435454u32, 244usize),
                    (268435454u32, 232usize),
                    (268435454u32, 140usize),
                    (268435422u32, 141usize),
                    (536870908u32, 144usize),
                    (536870908u32, 145usize),
                    (1342177270u32, 146usize),
                    (1610612724u32, 148usize),
                    (268435454u32, 245usize),
                    (268435454u32, 246usize),
                ];
                let mut _vl = 0;
                while _vl < 57usize {
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
                const VS_DESCS: [(usize, usize, usize); 1usize] = [(347usize, 0usize, 9usize)];
                const VS_DEPS: [usize; 9usize] = [
                    268usize, 269usize, 270usize, 271usize, 272usize, 273usize, 274usize, 275usize,
                    276usize,
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
                        return Err(E::gkr_permutation_cache_relation_failed(0usize, _vs));
                    }
                    _vs += 1;
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(0u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                let mut t_addr: BabyBearExt4 =
                    external_challenges.permutation_argument_linearization_challenges[0usize];
                field_ops::mul_assign_by_base(
                    &mut t_addr,
                    &BabyBearField::from_reduced_raw_repr(671088619u32),
                );
                field_ops::add_assign(&mut expected, &t_addr);
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(0usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(1usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(2usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(279usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 1usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(0u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                let mut t_addr: BabyBearExt4 =
                    external_challenges.permutation_argument_linearization_challenges[0usize];
                field_ops::mul_assign_by_base(
                    &mut t_addr,
                    &BabyBearField::from_reduced_raw_repr(939524073u32),
                );
                field_ops::add_assign(&mut expected, &t_addr);
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(6usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(7usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(8usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(280usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 2usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(0u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                let mut t_addr: BabyBearExt4 =
                    external_challenges.permutation_argument_linearization_challenges[0usize];
                field_ops::mul_assign_by_base(
                    &mut t_addr,
                    &BabyBearField::from_reduced_raw_repr(671088619u32),
                );
                field_ops::add_assign(&mut expected, &t_addr);
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(102usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(103usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(4usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(5usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(281usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 3usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(0u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                let mut t_addr: BabyBearExt4 =
                    external_challenges.permutation_argument_linearization_challenges[0usize];
                field_ops::mul_assign_by_base(
                    &mut t_addr,
                    &BabyBearField::from_reduced_raw_repr(939524073u32),
                );
                field_ops::add_assign(&mut expected, &t_addr);
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(102usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(103usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(8usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(282usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 4usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(14usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(10usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(11usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(12usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(13usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(283usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 5usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(14usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(17usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(18usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(19usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(20usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(284usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 6usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(14usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(102usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(103usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(15usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(16usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(285usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 7usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(14usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(102usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(103usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(21usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(22usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(286usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 8usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(27usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(23usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(24usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(25usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(26usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(287usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 9usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(27usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(30usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(31usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(32usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(33usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(288usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 10usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(27usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(102usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(103usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(28usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(29usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(289usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 11usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(27usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(102usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(103usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(34usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(35usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(290usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 12usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(40usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(36usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(37usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(38usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(39usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(291usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 13usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(40usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(43usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(44usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(45usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(46usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(292usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 14usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(40usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(102usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(103usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(41usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(42usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(293usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 15usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(40usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(102usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(103usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(47usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(48usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(294usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 16usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(53usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(49usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(50usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(51usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(52usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(295usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 17usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(53usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(56usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(57usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(58usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(59usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(296usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 18usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(53usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(102usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(103usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(54usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(55usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(297usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 19usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(53usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(102usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(103usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(60usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(61usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(298usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 20usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(66usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(62usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(63usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(64usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(65usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(299usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 21usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(66usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(69usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(70usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(71usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(72usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(300usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 22usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(66usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(102usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(103usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(67usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(68usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(301usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 23usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(66usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(102usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(103usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(73usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(74usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(302usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 24usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(79usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(75usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(76usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(77usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(78usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(303usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 25usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(79usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(82usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(83usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(84usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(85usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(304usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 26usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(79usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(102usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(103usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(80usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(81usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(305usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 27usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(79usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(102usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(103usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(86usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(87usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(306usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 28usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(92usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(88usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(89usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(90usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(91usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(307usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 29usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(92usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(95usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(96usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(97usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(98usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(308usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 30usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(92usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(102usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(103usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(93usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(94usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(309usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 31usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(268435454u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                {
                    let mut t_low: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[0usize];
                    let mut low = *state.prev_claims.get_unchecked(8usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    let mut var_offset = *state.prev_claims.get_unchecked(92usize);
                    field_ops::mul_assign_by_base(
                        &mut var_offset,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::add_assign(&mut low, &var_offset);
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(9usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(102usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(536870908u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(103usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(99usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(100usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(310usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 32usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(0u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                let mut t_addr: BabyBearExt4 =
                    external_challenges.permutation_argument_linearization_challenges[0usize];
                field_ops::mul_assign_by_base(
                    &mut t_addr,
                    &BabyBearField::from_reduced_raw_repr(268431198u32),
                );
                field_ops::add_assign(&mut expected, &t_addr);
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(102usize);
                    field_ops::add_assign_base(
                        &mut ts_low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_ts, &ts_low);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[3usize];
                    let ts_high = *state.prev_claims.get_unchecked(103usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                let cached = *state.prev_claims.get_unchecked(311usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 33usize));
                }
            }
            {
                let mut expected: BabyBearExt4 =
                    external_challenges.permutation_argument_additive_part;
                let c_addr_space = BabyBearField::from_reduced_raw_repr(0u32);
                field_ops::add_assign_base(&mut expected, &c_addr_space);
                let mut t_addr: BabyBearExt4 =
                    external_challenges.permutation_argument_linearization_challenges[0usize];
                field_ops::mul_assign_by_base(
                    &mut t_addr,
                    &BabyBearField::from_reduced_raw_repr(268431198u32),
                );
                field_ops::add_assign(&mut expected, &t_addr);
                let cached = *state.prev_claims.get_unchecked(312usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 34usize));
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
        #[allow(unused_mut)]
        let mut inits_and_teardowns_read_product: BabyBearExt4 = BabyBearExt4::ONE;
        #[allow(unused_mut)]
        let mut inits_and_teardowns_write_product: BabyBearExt4 = BabyBearExt4::ONE;
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
            inits_and_teardowns_read_product,
            inits_and_teardowns_write_product,
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
    fn verify_gkr<I: NonDeterminismSource<BabyBearField>, E: ErrorCreator>(
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
    fn verify_whir<I: NonDeterminismSource<BabyBearField>, E: ErrorCreator>(
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
