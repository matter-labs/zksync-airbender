use super::common::{
    dot_eq, draw_field_els_into, draw_single_field_el, ext_from_nds, ext_from_raw_words,
    fold_standard_claims, make_eq_poly, read_field_el, read_reduced_field_el,
    verify_final_step_check, verify_sumcheck_rounds, EXT_DEGREE,
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
use verifier_common::GKRExternalChallenges;
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_0_compute_claim(
    output_claims: &[BabyBearExt4; 52usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 64usize] = [
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
        (1usize, 31usize, 0usize),
        (2usize, 32usize, 33usize),
        (2usize, 34usize, 35usize),
        (2usize, 36usize, 37usize),
        (2usize, 38usize, 39usize),
        (2usize, 40usize, 41usize),
        (2usize, 42usize, 43usize),
        (2usize, 44usize, 45usize),
        (2usize, 46usize, 47usize),
        (2usize, 48usize, 49usize),
        (2usize, 50usize, 51usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 32usize] = [
            (SimpleGateType::Copy, [61usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [65usize, 66usize, 0usize, 0usize]),
            (SimpleGateType::Product, [67usize, 68usize, 0usize, 0usize]),
            (SimpleGateType::Product, [69usize, 70usize, 0usize, 0usize]),
            (SimpleGateType::Product, [71usize, 72usize, 0usize, 0usize]),
            (SimpleGateType::Product, [73usize, 74usize, 0usize, 0usize]),
            (SimpleGateType::Product, [75usize, 76usize, 0usize, 0usize]),
            (SimpleGateType::Product, [77usize, 78usize, 0usize, 0usize]),
            (SimpleGateType::Product, [79usize, 80usize, 0usize, 0usize]),
            (SimpleGateType::Product, [81usize, 82usize, 0usize, 0usize]),
            (SimpleGateType::Product, [83usize, 84usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupWithSetup,
                [62usize, 39usize, 64usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [63usize, 85usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [86usize, 87usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [88usize, 89usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [90usize, 91usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [92usize, 93usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [94usize, 95usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [96usize, 97usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [98usize, 99usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [100usize, 101usize, 0usize, 0usize],
            ),
            (SimpleGateType::Copy, [102usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupWithSetup,
                [103usize, 40usize, 104usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [105usize, 106usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [107usize, 108usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [109usize, 110usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [111usize, 112usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [113usize, 114usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [115usize, 116usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [117usize, 118usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [119usize, 120usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [121usize, 122usize, 0usize, 0usize],
            ),
        ];
        let mut _sg = 0;
        while _sg < 32usize {
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
            const VAL_QO: [(usize, usize); 1usize] = [(61usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(61usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(61usize, 1744830467usize)];
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
            const VAL_LN: [(usize, usize); 1usize] = [(59usize, 268435454usize)];
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
            const VAL_LN: [(usize, usize); 1usize] = [(60usize, 268435454usize)];
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
            const VAL_LN: [(usize, usize); 12usize] = [
                (0usize, 1744970275usize),
                (1usize, 1476674629usize),
                (12usize, 268435454usize),
                (13usize, 268435422usize),
                (14usize, 134217455usize),
                (16usize, 1744970275usize),
                (17usize, 1476674629usize),
                (41usize, 268435454usize),
                (43usize, 1744830467usize),
                (45usize, 268435454usize),
                (55usize, 268435454usize),
                (57usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 16usize] = [
                (0usize, 268435454usize),
                (1usize, 536870908usize),
                (2usize, 1744970275usize),
                (3usize, 1476674629usize),
                (10usize, 268435422usize),
                (11usize, 134217455usize),
                (15usize, 268435454usize),
                (16usize, 268435454usize),
                (17usize, 536870908usize),
                (18usize, 1744970275usize),
                (19usize, 1476674629usize),
                (42usize, 268435454usize),
                (44usize, 1744830467usize),
                (46usize, 268435454usize),
                (56usize, 268435454usize),
                (58usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (27usize, 268435454usize),
                (28usize, 536869820usize),
                (47usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (26usize, 536869820usize),
                (29usize, 268435454usize),
                (48usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 8usize] = [
                (6usize, 268435454usize),
                (7usize, 268434910usize),
                (8usize, 1744970275usize),
                (21usize, 268435454usize),
                (22usize, 268434910usize),
                (24usize, 1744970275usize),
                (49usize, 268435454usize),
                (51usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 10usize] = [
                (4usize, 268435454usize),
                (5usize, 268434910usize),
                (8usize, 268435454usize),
                (9usize, 1744970275usize),
                (20usize, 268434910usize),
                (23usize, 268435454usize),
                (24usize, 268435454usize),
                (25usize, 1744970275usize),
                (50usize, 268435454usize),
                (52usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (21usize, 268435454usize),
                (22usize, 268434910usize),
                (53usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (20usize, 268434910usize),
                (23usize, 268435454usize),
                (54usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(8usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(8usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(8usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(9usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(9usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(9usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(16usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(16usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(16usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(17usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(17usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(17usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(18usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(18usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(18usize, 1744830467usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(19usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(19usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(19usize, 1744830467usize)];
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
    acc
}
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_1_compute_claim(
    output_claims: &[BabyBearExt4; 29usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 19usize] = [
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
        (1usize, 17usize, 0usize),
        (1usize, 18usize, 0usize),
        (2usize, 19usize, 20usize),
        (2usize, 21usize, 22usize),
        (2usize, 23usize, 24usize),
        (2usize, 25usize, 26usize),
        (2usize, 27usize, 28usize),
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 19usize] = [
            (SimpleGateType::Copy, [0usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [1usize, 3usize, 0usize, 0usize]),
            (SimpleGateType::Product, [5usize, 7usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [9usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [2usize, 4usize, 0usize, 0usize]),
            (SimpleGateType::Product, [6usize, 8usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [10usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupUnbalanced,
                [29usize, 30usize, 31usize, 0usize],
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
                [50usize, 51usize, 48usize, 49usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [46usize, 47usize, 44usize, 45usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [42usize, 43usize, 40usize, 41usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [38usize, 39usize, 36usize, 37usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [34usize, 35usize, 32usize, 33usize],
            ),
        ];
        let mut _sg = 0;
        while _sg < 19usize {
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
    output_claims: &[BabyBearExt4; 17usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 12usize] = [
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
        (1usize, 15usize, 0usize),
        (1usize, 16usize, 0usize),
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 12usize] = [
            (SimpleGateType::Copy, [0usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [1usize, 2usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [3usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [4usize, 5usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [6usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupAggregatePair,
                [17usize, 18usize, 15usize, 16usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [13usize, 14usize, 11usize, 12usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [9usize, 10usize, 7usize, 8usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [27usize, 28usize, 25usize, 26usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [23usize, 24usize, 21usize, 22usize],
            ),
            (SimpleGateType::Copy, [19usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [20usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 12usize {
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
    output_claims: &[BabyBearExt4; 11usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 9usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (1usize, 2usize, 0usize),
        (2usize, 3usize, 4usize),
        (1usize, 5usize, 0usize),
        (1usize, 6usize, 0usize),
        (2usize, 7usize, 8usize),
        (1usize, 9usize, 0usize),
        (1usize, 10usize, 0usize),
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 9usize] = [
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
                [15usize, 16usize, 13usize, 14usize],
            ),
            (SimpleGateType::Copy, [11usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [12usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 9usize {
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
    output_claims: &[BabyBearExt4; 6usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 4usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (2usize, 2usize, 3usize),
        (2usize, 4usize, 5usize),
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 4usize] = [
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
        ];
        let mut _sg = 0;
        while _sg < 4usize {
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
    output_claims: &[BabyBearExt4; 6usize],
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
    acc
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
        if result != *state.prev_claims.get_unchecked(121usize) {
            return Err(E::gkr_virtual_setup_eval_mismatch(121usize));
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
        draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, init_challenges.as_mut_slice());
        let lookup_alpha = *init_challenges.get(0);
        let lookup_additive_challenge = *init_challenges.get(1);
        let address_high_bits_shift: u32 = 0u32;
        let mut evals_commit_buf = CommitBuf::<GKR_EVALS_COMMIT_BUF>::new();
        let evals_data_words = 96usize * EXT_DEGREE;
        {
            let mut i = 0;
            while i < evals_data_words {
                evals_commit_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                i += 1;
            }
        }
        ts.commit(&mut evals_commit_buf, evals_data_words);
        let evals_slice: &[BabyBearExt4] = unsafe { evals_commit_buf.data_as(96usize) };
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
        const DIM_REDUCE_INDICES_5: [usize; 6usize] =
            [0usize, 1usize, 2usize, 3usize, 4usize, 5usize];
        const DIM_REDUCE_INDICES_6: [usize; 6usize] =
            [0usize, 1usize, 2usize, 3usize, 4usize, 5usize];
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
        #[cfg(feature = "verifier_stats")]
        verifier_common::stats::log("GKR COMPRESSION INIT");
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<6usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 4usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    22usize,
                    nd_source,
                )?;
            let mut fc_len = 4usize;
            let data_words = 6usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(6usize);
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                state.prev_claims.as_array::<6usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 5usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    21usize,
                    nd_source,
                )?;
            let mut fc_len = 5usize;
            let data_words = 6usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(6usize);
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                state.prev_claims.as_array::<6usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 6usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    20usize,
                    nd_source,
                )?;
            let mut fc_len = 6usize;
            let data_words = 6usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(6usize);
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                state.prev_claims.as_array::<6usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 7usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    19usize,
                    nd_source,
                )?;
            let mut fc_len = 7usize;
            let data_words = 6usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(6usize);
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                state.prev_claims.as_array::<6usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 8usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    18usize,
                    nd_source,
                )?;
            let mut fc_len = 8usize;
            let data_words = 6usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(6usize);
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                state.prev_claims.as_array::<6usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 9usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    17usize,
                    nd_source,
                )?;
            let mut fc_len = 9usize;
            let data_words = 6usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(6usize);
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                state.prev_claims.as_array::<6usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 10usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    16usize,
                    nd_source,
                )?;
            let mut fc_len = 10usize;
            let data_words = 6usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(6usize);
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                state.prev_claims.as_array::<6usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 11usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    15usize,
                    nd_source,
                )?;
            let mut fc_len = 11usize;
            let data_words = 6usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(6usize);
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                state.prev_claims.as_array::<6usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 12usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    14usize,
                    nd_source,
                )?;
            let mut fc_len = 12usize;
            let data_words = 6usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(6usize);
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                state.prev_claims.as_array::<6usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 13usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    13usize,
                    nd_source,
                )?;
            let mut fc_len = 13usize;
            let data_words = 6usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(6usize);
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                state.prev_claims.as_array::<6usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 14usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    12usize,
                    nd_source,
                )?;
            let mut fc_len = 14usize;
            let data_words = 6usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(6usize);
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                state.prev_claims.as_array::<6usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 15usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    11usize,
                    nd_source,
                )?;
            let mut fc_len = 15usize;
            let data_words = 6usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(6usize);
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                state.prev_claims.as_array::<6usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 16usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    10usize,
                    nd_source,
                )?;
            let mut fc_len = 16usize;
            let data_words = 6usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(6usize);
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                state.prev_claims.as_array::<6usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 17usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    9usize,
                    nd_source,
                )?;
            let mut fc_len = 17usize;
            let data_words = 6usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(6usize);
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                state.prev_claims.as_array::<6usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 18usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    8usize,
                    nd_source,
                )?;
            let mut fc_len = 18usize;
            let data_words = 6usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(6usize);
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                state.prev_claims.as_array::<6usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    7usize,
                    nd_source,
                )?;
            let mut fc_len = 19usize;
            let data_words = 6usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(6usize);
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
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
                state.prev_claims.as_array::<6usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 20usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    6usize,
                    nd_source,
                )?;
            let mut fc_len = 20usize;
            let data_words = 6usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(6usize);
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 6");
        }
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<6usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 21usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    5usize,
                    nd_source,
                )?;
            let mut fc_len = 21usize;
            let data_words = 6usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(6usize);
                let f = dim_reducing_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    &DIM_REDUCE_INDICES_5,
                );
                verify_final_step_check::<E>(f, final_eq_prefactor, final_claim, 5usize)?;
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
            let evals: &[[BabyBearExt4; DIM_REDUCING_EQ_SIZE]] = eval_buf.data_as(6usize);
            let eq2_arr: &[BabyBearExt4; DIM_REDUCING_EQ_SIZE] =
                eq2.as_slice().try_into().unwrap_unchecked();
            state.prev_claims.clear();
            for i in 0..6usize {
                let e = evals.get_unchecked(i);
                state.prev_claims.push(dot_eq(e, eq2_arr));
            }
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 5");
        }
        {
            let initial_claim = layer_4_compute_claim(
                state.prev_claims.as_array::<6usize>(),
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
            let data_words = 11usize * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(11usize);
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
            fold_standard_claims::<11usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<11usize>(),
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
            let data_words = 17usize * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(17usize);
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
            fold_standard_claims::<17usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<17usize>(),
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
            let data_words = 29usize * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(29usize);
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
            fold_standard_claims::<29usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<29usize>(),
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
            let data_words = 52usize * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(52usize);
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
            fold_standard_claims::<52usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<52usize>(),
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
            let data_words = 123usize * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 1]] = eval_buf.data_as(123usize);
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
                let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + 57usize * EXT_DEGREE;
                total.div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS) * BLAKE2S_BLOCK_SIZE_U32_WORDS
            };
            let mut extra_buf = CommitBuf::<EXTRA_COMMIT_BUF>::new();
            let extra_data_words = 57usize * EXT_DEGREE;
            {
                let mut i = 0;
                while i < extra_data_words {
                    extra_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            let mut extra_evals = LazyVec::<BabyBearExt4, 57usize>::new();
            {
                let slice: &[BabyBearExt4] = unsafe { extra_buf.data_as(57usize) };
                for el in slice {
                    extra_evals.push(*el);
                }
            }
            ts.commit(&mut extra_buf, extra_data_words);
            let final_step_evals: &[[BabyBearExt4; 1]] = unsafe { eval_buf.data_as(123usize) };
            state.prev_claims.clear();
            {
                const LAYOUT_KIND: [usize; 180usize] = [
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 1usize, 0usize,
                    0usize, 1usize, 1usize, 0usize, 0usize, 1usize, 0usize, 0usize, 1usize, 1usize,
                    0usize, 0usize, 1usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize,
                    1usize, 1usize, 1usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 0usize,
                    1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 1usize,
                    1usize, 1usize, 0usize, 0usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 1usize, 1usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                ];
                const LAYOUT_POS: [usize; 180usize] = [
                    16usize, 17usize, 18usize, 19usize, 20usize, 21usize, 41usize, 42usize,
                    22usize, 43usize, 44usize, 23usize, 24usize, 45usize, 46usize, 25usize,
                    47usize, 48usize, 26usize, 27usize, 49usize, 50usize, 28usize, 51usize,
                    52usize, 29usize, 30usize, 31usize, 32usize, 33usize, 53usize, 54usize,
                    34usize, 35usize, 36usize, 37usize, 38usize, 39usize, 55usize, 56usize,
                    40usize, 41usize, 42usize, 57usize, 58usize, 43usize, 44usize, 45usize,
                    46usize, 59usize, 47usize, 60usize, 61usize, 62usize, 63usize, 0usize, 1usize,
                    2usize, 3usize, 0usize, 1usize, 2usize, 4usize, 5usize, 3usize, 6usize, 7usize,
                    8usize, 9usize, 4usize, 5usize, 6usize, 7usize, 8usize, 9usize, 10usize,
                    11usize, 12usize, 10usize, 11usize, 13usize, 14usize, 15usize, 16usize,
                    17usize, 18usize, 19usize, 12usize, 13usize, 20usize, 21usize, 22usize,
                    23usize, 24usize, 25usize, 14usize, 15usize, 26usize, 27usize, 28usize,
                    29usize, 30usize, 31usize, 32usize, 33usize, 34usize, 35usize, 36usize,
                    37usize, 38usize, 39usize, 40usize, 48usize, 49usize, 50usize, 51usize,
                    52usize, 53usize, 54usize, 55usize, 56usize, 64usize, 65usize, 66usize,
                    67usize, 68usize, 69usize, 70usize, 71usize, 72usize, 73usize, 74usize,
                    75usize, 76usize, 77usize, 78usize, 79usize, 80usize, 81usize, 82usize,
                    83usize, 84usize, 85usize, 86usize, 87usize, 88usize, 89usize, 90usize,
                    91usize, 92usize, 93usize, 94usize, 95usize, 96usize, 97usize, 98usize,
                    99usize, 100usize, 101usize, 102usize, 103usize, 104usize, 105usize, 106usize,
                    107usize, 108usize, 109usize, 110usize, 111usize, 112usize, 113usize, 114usize,
                    115usize, 116usize, 117usize, 118usize, 119usize, 120usize, 121usize, 122usize,
                ];
                let mut i = 0usize;
                while i < 180usize {
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
                const SC_DESCS: [(usize, u32, usize, usize); 18usize] = [
                    (142usize, 1476395013u32, 0usize, 3usize),
                    (143usize, 133099247u32, 3usize, 3usize),
                    (144usize, 1476395013u32, 6usize, 3usize),
                    (145usize, 133099247u32, 9usize, 3usize),
                    (146usize, 1476395013u32, 12usize, 3usize),
                    (147usize, 133099247u32, 15usize, 3usize),
                    (148usize, 1476395013u32, 18usize, 3usize),
                    (149usize, 133099247u32, 21usize, 3usize),
                    (150usize, 1476395013u32, 24usize, 3usize),
                    (151usize, 133099247u32, 27usize, 3usize),
                    (152usize, 1476395013u32, 30usize, 3usize),
                    (153usize, 133099247u32, 33usize, 3usize),
                    (154usize, 1476395013u32, 36usize, 3usize),
                    (155usize, 133099247u32, 39usize, 3usize),
                    (156usize, 1476395013u32, 42usize, 3usize),
                    (157usize, 133099247u32, 45usize, 3usize),
                    (158usize, 1476395013u32, 48usize, 3usize),
                    (159usize, 133099247u32, 51usize, 3usize),
                ];
                const SC_TERMS: [(u32, usize); 54usize] = [
                    (1744830467u32, 53usize),
                    (268435454u32, 0usize),
                    (133099247u32, 101usize),
                    (1744830467u32, 54usize),
                    (268435454u32, 1usize),
                    (1744830467u32, 101usize),
                    (1744830467u32, 53usize),
                    (268435454u32, 4usize),
                    (133099247u32, 102usize),
                    (1744830467u32, 54usize),
                    (268435454u32, 5usize),
                    (1744830467u32, 102usize),
                    (1744830467u32, 53usize),
                    (268435454u32, 11usize),
                    (133099247u32, 103usize),
                    (1744830467u32, 54usize),
                    (268435454u32, 12usize),
                    (1744830467u32, 103usize),
                    (1744830467u32, 53usize),
                    (268435454u32, 18usize),
                    (133099247u32, 104usize),
                    (1744830467u32, 54usize),
                    (268435454u32, 19usize),
                    (1744830467u32, 104usize),
                    (1744830467u32, 53usize),
                    (268435454u32, 25usize),
                    (133099247u32, 105usize),
                    (1744830467u32, 54usize),
                    (268435454u32, 26usize),
                    (1744830467u32, 105usize),
                    (1744830467u32, 53usize),
                    (268435454u32, 32usize),
                    (133099247u32, 106usize),
                    (1744830467u32, 54usize),
                    (268435454u32, 33usize),
                    (1744830467u32, 106usize),
                    (1744830467u32, 53usize),
                    (268435454u32, 36usize),
                    (133099247u32, 107usize),
                    (1744830467u32, 54usize),
                    (268435454u32, 37usize),
                    (1744830467u32, 107usize),
                    (1744830467u32, 53usize),
                    (268435454u32, 41usize),
                    (133099247u32, 108usize),
                    (1744830467u32, 54usize),
                    (268435454u32, 42usize),
                    (1744830467u32, 108usize),
                    (1744830467u32, 53usize),
                    (268435454u32, 46usize),
                    (133099247u32, 109usize),
                    (1744830467u32, 54usize),
                    (268435454u32, 47usize),
                    (1744830467u32, 109usize),
                ];
                let mut _sc = 0;
                while _sc < 18usize {
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
                const VL_DESCS: [(usize, usize, usize); 19usize] = [
                    (160usize, 0usize, 9usize),
                    (162usize, 9usize, 9usize),
                    (163usize, 18usize, 9usize),
                    (164usize, 27usize, 9usize),
                    (165usize, 36usize, 9usize),
                    (166usize, 45usize, 9usize),
                    (167usize, 54usize, 9usize),
                    (168usize, 63usize, 9usize),
                    (169usize, 72usize, 9usize),
                    (170usize, 81usize, 9usize),
                    (171usize, 90usize, 9usize),
                    (172usize, 99usize, 9usize),
                    (173usize, 108usize, 9usize),
                    (174usize, 117usize, 9usize),
                    (175usize, 126usize, 9usize),
                    (176usize, 135usize, 9usize),
                    (177usize, 144usize, 9usize),
                    (178usize, 153usize, 9usize),
                    (179usize, 162usize, 9usize),
                ];
                const VL_COLS: [(u32, usize, usize); 171usize] = [
                    (0u32, 0usize, 2usize),
                    (0u32, 2usize, 1usize),
                    (0u32, 3usize, 1usize),
                    (0u32, 4usize, 1usize),
                    (0u32, 5usize, 1usize),
                    (0u32, 6usize, 1usize),
                    (0u32, 7usize, 1usize),
                    (0u32, 8usize, 1usize),
                    (1476394949u32, 9usize, 0usize),
                    (0u32, 9usize, 1usize),
                    (0u32, 10usize, 1usize),
                    (0u32, 11usize, 1usize),
                    (0u32, 12usize, 0usize),
                    (0u32, 12usize, 0usize),
                    (0u32, 12usize, 0usize),
                    (0u32, 12usize, 0usize),
                    (0u32, 12usize, 0usize),
                    (1073741816u32, 12usize, 0usize),
                    (0u32, 12usize, 2usize),
                    (0u32, 14usize, 6usize),
                    (0u32, 20usize, 1usize),
                    (0u32, 21usize, 0usize),
                    (0u32, 21usize, 0usize),
                    (0u32, 21usize, 0usize),
                    (0u32, 21usize, 0usize),
                    (0u32, 21usize, 0usize),
                    (1073741816u32, 21usize, 0usize),
                    (0u32, 21usize, 1usize),
                    (0u32, 22usize, 1usize),
                    (0u32, 23usize, 1usize),
                    (0u32, 24usize, 0usize),
                    (0u32, 24usize, 0usize),
                    (0u32, 24usize, 0usize),
                    (0u32, 24usize, 0usize),
                    (0u32, 24usize, 0usize),
                    (1073741816u32, 24usize, 0usize),
                    (0u32, 24usize, 2usize),
                    (0u32, 26usize, 8usize),
                    (0u32, 34usize, 1usize),
                    (0u32, 35usize, 0usize),
                    (0u32, 35usize, 0usize),
                    (0u32, 35usize, 0usize),
                    (0u32, 35usize, 0usize),
                    (0u32, 35usize, 0usize),
                    (1073741816u32, 35usize, 0usize),
                    (0u32, 35usize, 1usize),
                    (0u32, 36usize, 1usize),
                    (0u32, 37usize, 1usize),
                    (0u32, 38usize, 0usize),
                    (0u32, 38usize, 0usize),
                    (0u32, 38usize, 0usize),
                    (0u32, 38usize, 0usize),
                    (0u32, 38usize, 0usize),
                    (536870876u32, 38usize, 0usize),
                    (0u32, 38usize, 1usize),
                    (0u32, 39usize, 1usize),
                    (0u32, 40usize, 1usize),
                    (0u32, 41usize, 0usize),
                    (0u32, 41usize, 0usize),
                    (0u32, 41usize, 0usize),
                    (0u32, 41usize, 0usize),
                    (0u32, 41usize, 0usize),
                    (1342177238u32, 41usize, 0usize),
                    (0u32, 41usize, 3usize),
                    (0u32, 44usize, 6usize),
                    (0u32, 50usize, 1usize),
                    (0u32, 51usize, 0usize),
                    (0u32, 51usize, 0usize),
                    (0u32, 51usize, 0usize),
                    (0u32, 51usize, 0usize),
                    (0u32, 51usize, 0usize),
                    (805306330u32, 51usize, 0usize),
                    (0u32, 51usize, 1usize),
                    (0u32, 52usize, 1usize),
                    (0u32, 53usize, 1usize),
                    (0u32, 54usize, 0usize),
                    (0u32, 54usize, 0usize),
                    (0u32, 54usize, 0usize),
                    (0u32, 54usize, 0usize),
                    (0u32, 54usize, 0usize),
                    (536870876u32, 54usize, 0usize),
                    (0u32, 54usize, 1usize),
                    (0u32, 55usize, 1usize),
                    (0u32, 56usize, 1usize),
                    (0u32, 57usize, 0usize),
                    (0u32, 57usize, 0usize),
                    (0u32, 57usize, 0usize),
                    (0u32, 57usize, 0usize),
                    (0u32, 57usize, 0usize),
                    (1342177238u32, 57usize, 0usize),
                    (0u32, 57usize, 3usize),
                    (0u32, 60usize, 7usize),
                    (0u32, 67usize, 1usize),
                    (0u32, 68usize, 0usize),
                    (0u32, 68usize, 0usize),
                    (0u32, 68usize, 0usize),
                    (0u32, 68usize, 0usize),
                    (0u32, 68usize, 0usize),
                    (805306330u32, 68usize, 0usize),
                    (0u32, 68usize, 1usize),
                    (0u32, 69usize, 1usize),
                    (0u32, 70usize, 1usize),
                    (0u32, 71usize, 0usize),
                    (0u32, 71usize, 0usize),
                    (0u32, 71usize, 0usize),
                    (0u32, 71usize, 0usize),
                    (0u32, 71usize, 0usize),
                    (1073741816u32, 71usize, 0usize),
                    (0u32, 71usize, 1usize),
                    (0u32, 72usize, 12usize),
                    (0u32, 84usize, 1usize),
                    (0u32, 85usize, 0usize),
                    (0u32, 85usize, 0usize),
                    (0u32, 85usize, 0usize),
                    (0u32, 85usize, 0usize),
                    (0u32, 85usize, 0usize),
                    (1073741816u32, 85usize, 0usize),
                    (0u32, 85usize, 1usize),
                    (0u32, 86usize, 1usize),
                    (0u32, 87usize, 1usize),
                    (0u32, 88usize, 0usize),
                    (0u32, 88usize, 0usize),
                    (0u32, 88usize, 0usize),
                    (0u32, 88usize, 0usize),
                    (0u32, 88usize, 0usize),
                    (1073741816u32, 88usize, 0usize),
                    (0u32, 88usize, 1usize),
                    (0u32, 89usize, 16usize),
                    (0u32, 105usize, 1usize),
                    (0u32, 106usize, 0usize),
                    (0u32, 106usize, 0usize),
                    (0u32, 106usize, 0usize),
                    (0u32, 106usize, 0usize),
                    (0u32, 106usize, 0usize),
                    (1073741816u32, 106usize, 0usize),
                    (0u32, 106usize, 2usize),
                    (0u32, 108usize, 1usize),
                    (0u32, 109usize, 1usize),
                    (0u32, 110usize, 0usize),
                    (0u32, 110usize, 0usize),
                    (0u32, 110usize, 0usize),
                    (0u32, 110usize, 0usize),
                    (0u32, 110usize, 0usize),
                    (1073741784u32, 110usize, 0usize),
                    (0u32, 110usize, 1usize),
                    (0u32, 111usize, 8usize),
                    (0u32, 119usize, 1usize),
                    (0u32, 120usize, 0usize),
                    (0u32, 120usize, 0usize),
                    (0u32, 120usize, 0usize),
                    (0u32, 120usize, 0usize),
                    (0u32, 120usize, 0usize),
                    (1342177238u32, 120usize, 0usize),
                    (0u32, 120usize, 2usize),
                    (0u32, 122usize, 1usize),
                    (0u32, 123usize, 1usize),
                    (0u32, 124usize, 0usize),
                    (0u32, 124usize, 0usize),
                    (0u32, 124usize, 0usize),
                    (0u32, 124usize, 0usize),
                    (0u32, 124usize, 0usize),
                    (1073741784u32, 124usize, 0usize),
                    (0u32, 124usize, 1usize),
                    (0u32, 125usize, 10usize),
                    (0u32, 135usize, 1usize),
                    (0u32, 136usize, 0usize),
                    (0u32, 136usize, 0usize),
                    (0u32, 136usize, 0usize),
                    (0u32, 136usize, 0usize),
                    (0u32, 136usize, 0usize),
                    (1342177238u32, 136usize, 0usize),
                ];
                const VL_TERMS: [(u32, usize); 136usize] = [
                    (268434910u32, 52usize),
                    (268435454u32, 48usize),
                    (268435454u32, 50usize),
                    (268435454u32, 8usize),
                    (268435454u32, 15usize),
                    (268435454u32, 22usize),
                    (268435454u32, 29usize),
                    (268435454u32, 40usize),
                    (268435454u32, 45usize),
                    (268435454u32, 61usize),
                    (268435454u32, 59usize),
                    (268435454u32, 62usize),
                    (16777216u32, 27usize),
                    (1996488705u32, 61usize),
                    (16777216u32, 6usize),
                    (16777216u32, 13usize),
                    (16777216u32, 38usize),
                    (1744831011u32, 55usize),
                    (1476396101u32, 56usize),
                    (1996488705u32, 59usize),
                    (268435454u32, 63usize),
                    (268435454u32, 64usize),
                    (268435454u32, 60usize),
                    (268435454u32, 65usize),
                    (16777216u32, 28usize),
                    (1996488705u32, 64usize),
                    (16777216u32, 7usize),
                    (16777216u32, 14usize),
                    (16777216u32, 39usize),
                    (16777216u32, 55usize),
                    (33554432u32, 56usize),
                    (1744831011u32, 57usize),
                    (1476396101u32, 58usize),
                    (1996488705u32, 60usize),
                    (268435454u32, 66usize),
                    (268435454u32, 73usize),
                    (268435454u32, 69usize),
                    (268435454u32, 75usize),
                    (268435454u32, 74usize),
                    (268435454u32, 70usize),
                    (268435454u32, 76usize),
                    (1048576u32, 13usize),
                    (2012217345u32, 73usize),
                    (2004877313u32, 74usize),
                    (1048576u32, 20usize),
                    (1048576u32, 65usize),
                    (268435456u32, 66usize),
                    (1744830499u32, 67usize),
                    (2012217345u32, 69usize),
                    (2004877313u32, 70usize),
                    (268435454u32, 77usize),
                    (268435454u32, 78usize),
                    (268435454u32, 71usize),
                    (268435454u32, 80usize),
                    (268435454u32, 79usize),
                    (268435454u32, 72usize),
                    (268435454u32, 81usize),
                    (1048576u32, 14usize),
                    (2012217345u32, 78usize),
                    (2004877313u32, 79usize),
                    (1048576u32, 21usize),
                    (1048576u32, 62usize),
                    (268435456u32, 63usize),
                    (1048576u32, 67usize),
                    (1744830499u32, 68usize),
                    (2012217345u32, 71usize),
                    (2004877313u32, 72usize),
                    (268435454u32, 82usize),
                    (268435454u32, 65usize),
                    (268435454u32, 87usize),
                    (268435454u32, 89usize),
                    (268435454u32, 66usize),
                    (16777216u32, 6usize),
                    (16777216u32, 13usize),
                    (16777216u32, 38usize),
                    (16777216u32, 43usize),
                    (1744831011u32, 55usize),
                    (1476396101u32, 56usize),
                    (16777216u32, 77usize),
                    (268435456u32, 80usize),
                    (134217727u32, 81usize),
                    (1744831011u32, 83usize),
                    (1476396101u32, 84usize),
                    (1996488705u32, 87usize),
                    (268435454u32, 90usize),
                    (268435454u32, 62usize),
                    (268435454u32, 88usize),
                    (268435454u32, 91usize),
                    (268435454u32, 63usize),
                    (16777216u32, 7usize),
                    (16777216u32, 14usize),
                    (16777216u32, 39usize),
                    (16777216u32, 44usize),
                    (16777216u32, 55usize),
                    (33554432u32, 56usize),
                    (1744831011u32, 57usize),
                    (1476396101u32, 58usize),
                    (268435456u32, 75usize),
                    (134217727u32, 76usize),
                    (16777216u32, 82usize),
                    (16777216u32, 83usize),
                    (33554432u32, 84usize),
                    (1744831011u32, 85usize),
                    (1476396101u32, 86usize),
                    (1996488705u32, 88usize),
                    (268435454u32, 92usize),
                    (268435454u32, 77usize),
                    (268435422u32, 80usize),
                    (268435454u32, 95usize),
                    (268435454u32, 97usize),
                    (268435454u32, 81usize),
                    (33554432u32, 20usize),
                    (33554432u32, 65usize),
                    (536870908u32, 66usize),
                    (1476396101u32, 67usize),
                    (33554432u32, 90usize),
                    (536870908u32, 91usize),
                    (1476396101u32, 93usize),
                    (1979711489u32, 95usize),
                    (268435454u32, 98usize),
                    (268435422u32, 75usize),
                    (268435454u32, 82usize),
                    (268435454u32, 96usize),
                    (268435454u32, 99usize),
                    (268435454u32, 76usize),
                    (33554432u32, 21usize),
                    (33554432u32, 62usize),
                    (536870908u32, 63usize),
                    (33554432u32, 67usize),
                    (1476396101u32, 68usize),
                    (536870908u32, 89usize),
                    (33554432u32, 92usize),
                    (33554432u32, 93usize),
                    (1476396101u32, 94usize),
                    (1979711489u32, 96usize),
                    (268435454u32, 100usize),
                ];
                let mut _vl = 0;
                while _vl < 19usize {
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
                const VS_DESCS: [(usize, usize, usize); 1usize] = [(161usize, 0usize, 9usize)];
                const VS_DEPS: [usize; 9usize] = [
                    112usize, 113usize, 114usize, 115usize, 116usize, 117usize, 118usize, 119usize,
                    120usize,
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
            check_virtual_setup_range_check_timestamp::<E>(&state)?;
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR MAIN LAYER 0");
        }
        state.batching_challenge = draw_single_field_el(ts);
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
