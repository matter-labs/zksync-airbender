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
    output_claims: &[BabyBearExt4; 73usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 83usize] = [
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
        (2usize, 47usize, 48usize),
        (1usize, 49usize, 0usize),
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
        (1usize, 72usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 45usize] = [
            (SimpleGateType::Copy, [80usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [85usize, 86usize, 0usize, 0usize]),
            (SimpleGateType::Product, [87usize, 88usize, 0usize, 0usize]),
            (SimpleGateType::Product, [89usize, 90usize, 0usize, 0usize]),
            (SimpleGateType::Product, [91usize, 92usize, 0usize, 0usize]),
            (SimpleGateType::Product, [93usize, 94usize, 0usize, 0usize]),
            (SimpleGateType::Product, [95usize, 96usize, 0usize, 0usize]),
            (SimpleGateType::Product, [97usize, 98usize, 0usize, 0usize]),
            (SimpleGateType::Product, [99usize, 100usize, 0usize, 0usize]),
            (
                SimpleGateType::Product,
                [101usize, 102usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [103usize, 104usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [105usize, 106usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [107usize, 108usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [109usize, 110usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [111usize, 112usize, 0usize, 0usize],
            ),
            (SimpleGateType::Copy, [113usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [114usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupWithSetup,
                [115usize, 39usize, 83usize, 0usize],
            ),
            (
                SimpleGateType::LookupWithSetup,
                [81usize, 40usize, 84usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [82usize, 116usize, 0usize, 0usize],
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
            (
                SimpleGateType::LookupInitialPair,
                [123usize, 124usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [125usize, 126usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [127usize, 128usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [129usize, 130usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [131usize, 132usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [133usize, 134usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [135usize, 136usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [137usize, 138usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [139usize, 140usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [141usize, 142usize, 0usize, 0usize],
            ),
            (SimpleGateType::Copy, [143usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupWithSetup,
                [144usize, 41usize, 145usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [146usize, 147usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [148usize, 149usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [150usize, 151usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [152usize, 153usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [154usize, 155usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [156usize, 157usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [158usize, 159usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [160usize, 161usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [162usize, 163usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [164usize, 165usize, 0usize, 0usize],
            ),
        ];
        let mut _sg = 0;
        while _sg < 45usize {
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
            const VAL_COLS: [(usize, usize); 8usize] = [
                (268435326usize, 0usize),
                (0usize, 0usize),
                (0usize, 4usize),
                (0usize, 4usize),
                (0usize, 4usize),
                (0usize, 4usize),
                (0usize, 4usize),
                (0usize, 4usize),
            ];
            const VAL_VL_TERMS: [(usize, usize); 24usize] = [
                (79usize, 1048576usize),
                (22usize, 2012217345usize),
                (23usize, 1996488705usize),
                (24usize, 1744830465usize),
                (76usize, 1048576usize),
                (19usize, 2012217345usize),
                (20usize, 1996488705usize),
                (21usize, 1744830465usize),
                (68usize, 1048576usize),
                (16usize, 2012217345usize),
                (17usize, 1996488705usize),
                (18usize, 1744830465usize),
                (60usize, 1048576usize),
                (13usize, 2012217345usize),
                (14usize, 1996488705usize),
                (15usize, 1744830465usize),
                (52usize, 1048576usize),
                (10usize, 2012217345usize),
                (11usize, 1996488705usize),
                (12usize, 1744830465usize),
                (46usize, 1048576usize),
                (7usize, 2012217345usize),
                (8usize, 1996488705usize),
                (9usize, 1744830465usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(80usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(80usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(80usize, 1744830467usize)];
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
            const VAL_LN: [(usize, usize); 1usize] = [(42usize, 268435454usize)];
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
            const VAL_LN: [(usize, usize); 1usize] = [(43usize, 268435454usize)];
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
                [(47usize, 1744830467usize), (49usize, 268435454usize)];
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
                [(48usize, 1744830467usize), (50usize, 268435454usize)];
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
                [(51usize, 1744830467usize), (53usize, 268435454usize)];
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
                [(52usize, 1744830467usize), (54usize, 268435454usize)];
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
                [(55usize, 1744830467usize), (57usize, 268435454usize)];
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
                [(56usize, 1744830467usize), (58usize, 268435454usize)];
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
                [(59usize, 1744830467usize), (61usize, 268435454usize)];
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
                [(60usize, 1744830467usize), (62usize, 268435454usize)];
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
                [(63usize, 1744830467usize), (65usize, 268435454usize)];
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
                [(64usize, 1744830467usize), (66usize, 268435454usize)];
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
                [(67usize, 1744830467usize), (69usize, 268435454usize)];
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
                [(68usize, 1744830467usize), (70usize, 268435454usize)];
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
                [(71usize, 1744830467usize), (73usize, 268435454usize)];
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
                [(72usize, 1744830467usize), (74usize, 268435454usize)];
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
                [(75usize, 1744830467usize), (77usize, 268435454usize)];
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
                [(76usize, 1744830467usize), (78usize, 268435454usize)];
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
                (0usize, 268435454usize),
                (3usize, 1744830467usize),
                (4usize, 1744830499usize),
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
                (1usize, 268435454usize),
                (5usize, 1744830467usize),
                (6usize, 1744830499usize),
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
            const VAL_LN: [(usize, usize); 5usize] = [
                (1usize, 1996488705usize),
                (5usize, 16777216usize),
                (6usize, 268435456usize),
                (44usize, 16777216usize),
                (45usize, 1996488705usize),
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
                (2usize, 268435454usize),
                (7usize, 1744830467usize),
                (8usize, 1744830499usize),
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
    acc
}
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_1_compute_claim(
    output_claims: &[BabyBearExt4; 39usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 25usize] = [
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
        (1usize, 37usize, 0usize),
        (1usize, 38usize, 0usize),
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 25usize] = [
            (SimpleGateType::Copy, [0usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [1usize, 3usize, 0usize, 0usize]),
            (SimpleGateType::Product, [5usize, 7usize, 0usize, 0usize]),
            (SimpleGateType::Product, [9usize, 11usize, 0usize, 0usize]),
            (SimpleGateType::Product, [13usize, 15usize, 0usize, 0usize]),
            (SimpleGateType::Product, [2usize, 4usize, 0usize, 0usize]),
            (SimpleGateType::Product, [6usize, 8usize, 0usize, 0usize]),
            (SimpleGateType::Product, [10usize, 12usize, 0usize, 0usize]),
            (SimpleGateType::Product, [14usize, 16usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupUnbalanced,
                [47usize, 48usize, 49usize, 0usize],
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
            (
                SimpleGateType::LookupAggregatePair,
                [29usize, 30usize, 27usize, 28usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [25usize, 26usize, 23usize, 24usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [21usize, 22usize, 19usize, 20usize],
            ),
            (
                SimpleGateType::LookupUnbalanced,
                [70usize, 71usize, 72usize, 0usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [68usize, 69usize, 66usize, 67usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [64usize, 65usize, 62usize, 63usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [60usize, 61usize, 58usize, 59usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [56usize, 57usize, 54usize, 55usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [52usize, 53usize, 50usize, 51usize],
            ),
            (SimpleGateType::Copy, [17usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [18usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 25usize {
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
    output_claims: &[BabyBearExt4; 21usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 14usize] = [
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
        (1usize, 19usize, 0usize),
        (1usize, 20usize, 0usize),
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 14usize] = [
            (SimpleGateType::Copy, [0usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [1usize, 2usize, 0usize, 0usize]),
            (SimpleGateType::Product, [3usize, 4usize, 0usize, 0usize]),
            (SimpleGateType::Product, [5usize, 6usize, 0usize, 0usize]),
            (SimpleGateType::Product, [7usize, 8usize, 0usize, 0usize]),
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
            (
                SimpleGateType::LookupAggregatePair,
                [11usize, 12usize, 9usize, 10usize],
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
            (SimpleGateType::Copy, [37usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [38usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 14usize {
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
    output_claims: &[BabyBearExt4; 13usize],
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
        (1usize, 11usize, 0usize),
        (1usize, 12usize, 0usize),
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
unsafe fn layer_4_compute_claim(
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
        if result != *state.prev_claims.get_unchecked(193usize) {
            return Err(E::gkr_virtual_setup_eval_mismatch(193usize));
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
        if result != *state.prev_claims.get_unchecked(194usize) {
            return Err(E::gkr_virtual_setup_eval_mismatch(194usize));
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
        const DIM_REDUCE_INDICES_5: [usize; 8usize] = [
            0usize, 1usize, 6usize, 7usize, 2usize, 3usize, 4usize, 5usize,
        ];
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
                    22usize,
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
                verify_sumcheck_rounds::<I, E, 5usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    21usize,
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
                verify_sumcheck_rounds::<I, E, 6usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    20usize,
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
                verify_sumcheck_rounds::<I, E, 7usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    19usize,
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
                verify_sumcheck_rounds::<I, E, 8usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    18usize,
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
                verify_sumcheck_rounds::<I, E, 9usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    17usize,
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
                verify_sumcheck_rounds::<I, E, 10usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    16usize,
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
                verify_sumcheck_rounds::<I, E, 11usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    15usize,
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
                verify_sumcheck_rounds::<I, E, 12usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    14usize,
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
                verify_sumcheck_rounds::<I, E, 13usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    13usize,
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
                verify_sumcheck_rounds::<I, E, 14usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    12usize,
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
                verify_sumcheck_rounds::<I, E, 15usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    11usize,
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
                verify_sumcheck_rounds::<I, E, 16usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    10usize,
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
                verify_sumcheck_rounds::<I, E, 17usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    9usize,
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
                verify_sumcheck_rounds::<I, E, 18usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    8usize,
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
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    7usize,
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
                verify_sumcheck_rounds::<I, E, 20usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    6usize,
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
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<8usize>(),
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
            verifier_common::stats::log("GKR COMPRESSION LAYER 5");
        }
        {
            let initial_claim = layer_4_compute_claim(
                state.prev_claims.as_array::<8usize>(),
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
            fold_standard_claims::<13usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<13usize>(),
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
            fold_standard_claims::<21usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<21usize>(),
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
            const NUM_AT_POINT_EVALS: usize = 39usize;
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
            fold_standard_claims::<39usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<39usize>(),
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
            const NUM_AT_POINT_EVALS: usize = 73usize;
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
            fold_standard_claims::<73usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<73usize>(),
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
            const NUM_AT_POINT_EVALS: usize = 166usize;
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
            const NUM_EXTRA_EVALS: usize = 110usize;
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
                const LAYOUT_KIND: [usize; 276usize] = [
                    1usize, 1usize, 1usize, 0usize, 1usize, 0usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 0usize,
                    1usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 1usize, 0usize, 0usize,
                    1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    1usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize,
                    1usize, 0usize, 0usize, 1usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 1usize, 0usize, 0usize, 1usize,
                    1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize,
                    0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 0usize,
                    0usize, 1usize, 0usize, 0usize, 1usize, 0usize, 0usize, 0usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                ];
                const LAYOUT_POS: [usize; 276usize] = [
                    52usize, 53usize, 54usize, 42usize, 55usize, 43usize, 56usize, 57usize,
                    58usize, 59usize, 60usize, 61usize, 62usize, 63usize, 64usize, 65usize,
                    66usize, 67usize, 68usize, 44usize, 69usize, 45usize, 46usize, 70usize,
                    71usize, 47usize, 48usize, 72usize, 49usize, 50usize, 73usize, 74usize,
                    51usize, 52usize, 53usize, 54usize, 75usize, 76usize, 55usize, 56usize,
                    77usize, 57usize, 58usize, 78usize, 79usize, 59usize, 60usize, 61usize,
                    62usize, 80usize, 81usize, 63usize, 64usize, 82usize, 65usize, 66usize,
                    83usize, 84usize, 67usize, 68usize, 69usize, 70usize, 85usize, 86usize,
                    71usize, 72usize, 87usize, 73usize, 74usize, 88usize, 89usize, 75usize,
                    76usize, 77usize, 78usize, 90usize, 91usize, 92usize, 93usize, 94usize,
                    95usize, 96usize, 97usize, 98usize, 99usize, 100usize, 101usize, 79usize,
                    80usize, 81usize, 82usize, 0usize, 1usize, 0usize, 1usize, 2usize, 2usize,
                    3usize, 4usize, 3usize, 4usize, 5usize, 5usize, 6usize, 6usize, 7usize, 8usize,
                    9usize, 7usize, 8usize, 9usize, 10usize, 11usize, 12usize, 13usize, 14usize,
                    15usize, 10usize, 11usize, 12usize, 16usize, 17usize, 18usize, 19usize,
                    20usize, 21usize, 22usize, 23usize, 24usize, 13usize, 14usize, 15usize,
                    25usize, 26usize, 27usize, 28usize, 29usize, 30usize, 31usize, 32usize,
                    33usize, 16usize, 17usize, 18usize, 34usize, 35usize, 36usize, 37usize,
                    38usize, 39usize, 40usize, 41usize, 42usize, 19usize, 20usize, 21usize,
                    43usize, 44usize, 45usize, 46usize, 47usize, 48usize, 49usize, 50usize,
                    51usize, 22usize, 23usize, 24usize, 25usize, 26usize, 27usize, 28usize,
                    29usize, 30usize, 31usize, 32usize, 33usize, 34usize, 35usize, 36usize,
                    37usize, 38usize, 39usize, 40usize, 41usize, 102usize, 103usize, 104usize,
                    105usize, 106usize, 107usize, 108usize, 109usize, 83usize, 84usize, 85usize,
                    86usize, 87usize, 88usize, 89usize, 90usize, 91usize, 92usize, 93usize,
                    94usize, 95usize, 96usize, 97usize, 98usize, 99usize, 100usize, 101usize,
                    102usize, 103usize, 104usize, 105usize, 106usize, 107usize, 108usize, 109usize,
                    110usize, 111usize, 112usize, 113usize, 114usize, 115usize, 116usize, 117usize,
                    118usize, 119usize, 120usize, 121usize, 122usize, 123usize, 124usize, 125usize,
                    126usize, 127usize, 128usize, 129usize, 130usize, 131usize, 132usize, 133usize,
                    134usize, 135usize, 136usize, 137usize, 138usize, 139usize, 140usize, 141usize,
                    142usize, 143usize, 144usize, 145usize, 146usize, 147usize, 148usize, 149usize,
                    150usize, 151usize, 152usize, 153usize, 154usize, 155usize, 156usize, 157usize,
                    158usize, 159usize, 160usize, 161usize, 162usize, 163usize, 164usize, 165usize,
                ];
                let mut i = 0usize;
                while i < 276usize {
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
                const SC_DESCS: [(usize, u32, usize, usize); 29usize] = [
                    (225usize, 0u32, 0usize, 1usize),
                    (226usize, 1476395013u32, 1usize, 3usize),
                    (227usize, 133099247u32, 4usize, 3usize),
                    (228usize, 1476395013u32, 7usize, 3usize),
                    (229usize, 133099247u32, 10usize, 3usize),
                    (230usize, 1476395013u32, 13usize, 3usize),
                    (231usize, 133099247u32, 16usize, 3usize),
                    (232usize, 1476395013u32, 19usize, 3usize),
                    (233usize, 133099247u32, 22usize, 3usize),
                    (234usize, 1476395013u32, 25usize, 3usize),
                    (235usize, 133099247u32, 28usize, 3usize),
                    (236usize, 1476395013u32, 31usize, 3usize),
                    (237usize, 133099247u32, 34usize, 3usize),
                    (238usize, 1476395013u32, 37usize, 3usize),
                    (239usize, 133099247u32, 40usize, 3usize),
                    (240usize, 1476395013u32, 43usize, 3usize),
                    (241usize, 133099247u32, 46usize, 3usize),
                    (242usize, 1476395013u32, 49usize, 3usize),
                    (243usize, 133099247u32, 52usize, 3usize),
                    (244usize, 1476395013u32, 55usize, 3usize),
                    (245usize, 133099247u32, 58usize, 3usize),
                    (246usize, 1476395013u32, 61usize, 3usize),
                    (247usize, 133099247u32, 64usize, 3usize),
                    (248usize, 1476395013u32, 67usize, 3usize),
                    (249usize, 133099247u32, 70usize, 3usize),
                    (250usize, 1476395013u32, 73usize, 3usize),
                    (251usize, 133099247u32, 76usize, 3usize),
                    (252usize, 1476395013u32, 79usize, 3usize),
                    (253usize, 133099247u32, 82usize, 3usize),
                ];
                const SC_TERMS: [(u32, usize); 85usize] = [
                    (16777216u32, 8usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 0usize),
                    (133099247u32, 168usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 1usize),
                    (1744830467u32, 168usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 6usize),
                    (133099247u32, 169usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 7usize),
                    (1744830467u32, 169usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 10usize),
                    (133099247u32, 170usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 11usize),
                    (1744830467u32, 170usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 17usize),
                    (133099247u32, 171usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 18usize),
                    (1744830467u32, 171usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 23usize),
                    (133099247u32, 172usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 24usize),
                    (1744830467u32, 172usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 30usize),
                    (133099247u32, 173usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 31usize),
                    (1744830467u32, 173usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 36usize),
                    (133099247u32, 174usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 37usize),
                    (1744830467u32, 174usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 43usize),
                    (133099247u32, 175usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 44usize),
                    (1744830467u32, 175usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 49usize),
                    (133099247u32, 176usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 50usize),
                    (1744830467u32, 176usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 56usize),
                    (133099247u32, 177usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 57usize),
                    (1744830467u32, 177usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 62usize),
                    (133099247u32, 178usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 63usize),
                    (1744830467u32, 178usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 69usize),
                    (133099247u32, 179usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 70usize),
                    (1744830467u32, 179usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 75usize),
                    (133099247u32, 180usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 76usize),
                    (1744830467u32, 180usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 82usize),
                    (133099247u32, 181usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 83usize),
                    (1744830467u32, 181usize),
                ];
                let mut _sc = 0;
                while _sc < 29usize {
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
                const VL_DESCS: [(usize, usize, usize); 21usize] = [
                    (254usize, 0usize, 8usize),
                    (256usize, 8usize, 8usize),
                    (257usize, 16usize, 8usize),
                    (258usize, 24usize, 8usize),
                    (259usize, 32usize, 8usize),
                    (260usize, 40usize, 8usize),
                    (261usize, 48usize, 8usize),
                    (262usize, 56usize, 8usize),
                    (263usize, 64usize, 8usize),
                    (264usize, 72usize, 8usize),
                    (265usize, 80usize, 8usize),
                    (266usize, 88usize, 8usize),
                    (267usize, 96usize, 8usize),
                    (268usize, 104usize, 8usize),
                    (269usize, 112usize, 8usize),
                    (270usize, 120usize, 8usize),
                    (271usize, 128usize, 8usize),
                    (272usize, 136usize, 8usize),
                    (273usize, 144usize, 8usize),
                    (274usize, 152usize, 8usize),
                    (275usize, 160usize, 8usize),
                ];
                const VL_COLS: [(u32, usize, usize); 168usize] = [
                    (0u32, 0usize, 2usize),
                    (0u32, 2usize, 1usize),
                    (0u32, 3usize, 1usize),
                    (0u32, 4usize, 1usize),
                    (0u32, 5usize, 1usize),
                    (0u32, 6usize, 1usize),
                    (0u32, 7usize, 1usize),
                    (1744830339u32, 8usize, 0usize),
                    (0u32, 8usize, 2usize),
                    (0u32, 10usize, 1usize),
                    (0u32, 11usize, 1usize),
                    (0u32, 12usize, 0usize),
                    (0u32, 12usize, 0usize),
                    (0u32, 12usize, 0usize),
                    (0u32, 12usize, 0usize),
                    (2013265793u32, 12usize, 0usize),
                    (0u32, 12usize, 1usize),
                    (0u32, 13usize, 1usize),
                    (0u32, 14usize, 2usize),
                    (0u32, 16usize, 0usize),
                    (0u32, 16usize, 0usize),
                    (0u32, 16usize, 0usize),
                    (0u32, 16usize, 0usize),
                    (134217647u32, 16usize, 0usize),
                    (0u32, 16usize, 2usize),
                    (536870844u32, 18usize, 1usize),
                    (0u32, 19usize, 3usize),
                    (0u32, 22usize, 0usize),
                    (0u32, 22usize, 0usize),
                    (0u32, 22usize, 0usize),
                    (0u32, 22usize, 0usize),
                    (134217647u32, 22usize, 0usize),
                    (0u32, 22usize, 2usize),
                    (1610612532u32, 24usize, 1usize),
                    (0u32, 25usize, 3usize),
                    (0u32, 28usize, 0usize),
                    (0u32, 28usize, 0usize),
                    (0u32, 28usize, 0usize),
                    (0u32, 28usize, 0usize),
                    (134217647u32, 28usize, 0usize),
                    (0u32, 28usize, 2usize),
                    (1744829987u32, 30usize, 1usize),
                    (0u32, 31usize, 3usize),
                    (0u32, 34usize, 0usize),
                    (0u32, 34usize, 0usize),
                    (0u32, 34usize, 0usize),
                    (0u32, 34usize, 0usize),
                    (134217647u32, 34usize, 0usize),
                    (0u32, 34usize, 1usize),
                    (0u32, 35usize, 1usize),
                    (0u32, 36usize, 1usize),
                    (0u32, 37usize, 1usize),
                    (0u32, 38usize, 1usize),
                    (0u32, 39usize, 1usize),
                    (0u32, 40usize, 0usize),
                    (268435326u32, 40usize, 0usize),
                    (0u32, 40usize, 1usize),
                    (0u32, 41usize, 1usize),
                    (0u32, 42usize, 1usize),
                    (0u32, 43usize, 1usize),
                    (0u32, 44usize, 1usize),
                    (0u32, 45usize, 1usize),
                    (0u32, 46usize, 0usize),
                    (268435326u32, 46usize, 0usize),
                    (0u32, 46usize, 1usize),
                    (0u32, 47usize, 1usize),
                    (0u32, 48usize, 1usize),
                    (0u32, 49usize, 1usize),
                    (0u32, 50usize, 1usize),
                    (0u32, 51usize, 1usize),
                    (0u32, 52usize, 0usize),
                    (268435326u32, 52usize, 0usize),
                    (0u32, 52usize, 4usize),
                    (0u32, 56usize, 4usize),
                    (0u32, 60usize, 4usize),
                    (0u32, 64usize, 4usize),
                    (0u32, 68usize, 4usize),
                    (0u32, 72usize, 4usize),
                    (0u32, 76usize, 0usize),
                    (268435326u32, 76usize, 0usize),
                    (0u32, 76usize, 1usize),
                    (0u32, 77usize, 1usize),
                    (0u32, 78usize, 1usize),
                    (0u32, 79usize, 1usize),
                    (0u32, 80usize, 1usize),
                    (0u32, 81usize, 1usize),
                    (0u32, 82usize, 0usize),
                    (268435326u32, 82usize, 0usize),
                    (0u32, 82usize, 1usize),
                    (0u32, 83usize, 1usize),
                    (0u32, 84usize, 1usize),
                    (0u32, 85usize, 1usize),
                    (0u32, 86usize, 1usize),
                    (0u32, 87usize, 1usize),
                    (0u32, 88usize, 0usize),
                    (268435326u32, 88usize, 0usize),
                    (0u32, 88usize, 1usize),
                    (0u32, 89usize, 1usize),
                    (0u32, 90usize, 1usize),
                    (0u32, 91usize, 1usize),
                    (0u32, 92usize, 1usize),
                    (0u32, 93usize, 1usize),
                    (0u32, 94usize, 0usize),
                    (268435326u32, 94usize, 0usize),
                    (0u32, 94usize, 4usize),
                    (0u32, 98usize, 4usize),
                    (0u32, 102usize, 4usize),
                    (0u32, 106usize, 4usize),
                    (0u32, 110usize, 4usize),
                    (0u32, 114usize, 4usize),
                    (0u32, 118usize, 0usize),
                    (268435326u32, 118usize, 0usize),
                    (0u32, 118usize, 1usize),
                    (0u32, 119usize, 1usize),
                    (0u32, 120usize, 1usize),
                    (0u32, 121usize, 1usize),
                    (0u32, 122usize, 1usize),
                    (0u32, 123usize, 1usize),
                    (0u32, 124usize, 0usize),
                    (268435326u32, 124usize, 0usize),
                    (0u32, 124usize, 1usize),
                    (0u32, 125usize, 1usize),
                    (0u32, 126usize, 1usize),
                    (0u32, 127usize, 1usize),
                    (0u32, 128usize, 1usize),
                    (0u32, 129usize, 1usize),
                    (0u32, 130usize, 0usize),
                    (268435326u32, 130usize, 0usize),
                    (0u32, 130usize, 1usize),
                    (0u32, 131usize, 1usize),
                    (0u32, 132usize, 1usize),
                    (0u32, 133usize, 1usize),
                    (0u32, 134usize, 1usize),
                    (0u32, 135usize, 1usize),
                    (0u32, 136usize, 0usize),
                    (268435326u32, 136usize, 0usize),
                    (0u32, 136usize, 4usize),
                    (0u32, 140usize, 4usize),
                    (0u32, 144usize, 4usize),
                    (0u32, 148usize, 4usize),
                    (0u32, 152usize, 4usize),
                    (0u32, 156usize, 4usize),
                    (0u32, 160usize, 0usize),
                    (268435326u32, 160usize, 0usize),
                    (0u32, 160usize, 1usize),
                    (0u32, 161usize, 1usize),
                    (0u32, 162usize, 1usize),
                    (0u32, 163usize, 1usize),
                    (0u32, 164usize, 1usize),
                    (0u32, 165usize, 1usize),
                    (0u32, 166usize, 0usize),
                    (268435326u32, 166usize, 0usize),
                    (0u32, 166usize, 1usize),
                    (0u32, 167usize, 1usize),
                    (0u32, 168usize, 1usize),
                    (0u32, 169usize, 1usize),
                    (0u32, 170usize, 1usize),
                    (0u32, 171usize, 1usize),
                    (0u32, 172usize, 0usize),
                    (268435326u32, 172usize, 0usize),
                    (0u32, 172usize, 1usize),
                    (0u32, 173usize, 1usize),
                    (0u32, 174usize, 1usize),
                    (0u32, 175usize, 1usize),
                    (0u32, 176usize, 1usize),
                    (0u32, 177usize, 1usize),
                    (0u32, 178usize, 0usize),
                    (268435326u32, 178usize, 0usize),
                ];
                const VL_TERMS: [(u32, usize); 178usize] = [
                    (134213359u32, 88usize),
                    (268435454u32, 2usize),
                    (268435454u32, 14usize),
                    (268435454u32, 27usize),
                    (268435454u32, 40usize),
                    (268435454u32, 53usize),
                    (268435454u32, 66usize),
                    (268435454u32, 79usize),
                    (134213359u32, 88usize),
                    (268435454u32, 2usize),
                    (268435454u32, 4usize),
                    (268435454u32, 91usize),
                    (268435454u32, 92usize),
                    (268435454u32, 91usize),
                    (268435454u32, 96usize),
                    (268435422u32, 97usize),
                    (16777216u32, 12usize),
                    (1996488705u32, 92usize),
                    (268435454u32, 91usize),
                    (16777216u32, 15usize),
                    (1996488705u32, 96usize),
                    (1744830465u32, 97usize),
                    (16777216u32, 13usize),
                    (1996488705u32, 93usize),
                    (268435454u32, 91usize),
                    (16777216u32, 16usize),
                    (1996488705u32, 99usize),
                    (1744830465u32, 100usize),
                    (16777216u32, 20usize),
                    (1996488705u32, 95usize),
                    (268435454u32, 91usize),
                    (16777216u32, 22usize),
                    (1996488705u32, 105usize),
                    (1744830465u32, 106usize),
                    (268435454u32, 96usize),
                    (268435454u32, 108usize),
                    (268435454u32, 120usize),
                    (268435454u32, 132usize),
                    (268435454u32, 144usize),
                    (268435454u32, 156usize),
                    (268435454u32, 97usize),
                    (268435454u32, 109usize),
                    (268435454u32, 121usize),
                    (268435454u32, 133usize),
                    (268435454u32, 145usize),
                    (268435454u32, 157usize),
                    (268435454u32, 98usize),
                    (268435454u32, 110usize),
                    (268435454u32, 122usize),
                    (268435454u32, 134usize),
                    (268435454u32, 146usize),
                    (268435454u32, 158usize),
                    (1048576u32, 15usize),
                    (2012217345u32, 96usize),
                    (1996488705u32, 97usize),
                    (1744830465u32, 98usize),
                    (1048576u32, 25usize),
                    (2012217345u32, 108usize),
                    (1996488705u32, 109usize),
                    (1744830465u32, 110usize),
                    (1048576u32, 38usize),
                    (2012217345u32, 120usize),
                    (1996488705u32, 121usize),
                    (1744830465u32, 122usize),
                    (1048576u32, 51usize),
                    (2012217345u32, 132usize),
                    (1996488705u32, 133usize),
                    (1744830465u32, 134usize),
                    (1048576u32, 64usize),
                    (2012217345u32, 144usize),
                    (1996488705u32, 145usize),
                    (1744830465u32, 146usize),
                    (1048576u32, 80usize),
                    (2012217345u32, 156usize),
                    (1996488705u32, 157usize),
                    (1744830465u32, 158usize),
                    (268435454u32, 99usize),
                    (268435454u32, 111usize),
                    (268435454u32, 123usize),
                    (268435454u32, 135usize),
                    (268435454u32, 147usize),
                    (268435454u32, 159usize),
                    (268435454u32, 100usize),
                    (268435454u32, 112usize),
                    (268435454u32, 124usize),
                    (268435454u32, 136usize),
                    (268435454u32, 148usize),
                    (268435454u32, 160usize),
                    (268435454u32, 101usize),
                    (268435454u32, 113usize),
                    (268435454u32, 125usize),
                    (268435454u32, 137usize),
                    (268435454u32, 149usize),
                    (268435454u32, 161usize),
                    (1048576u32, 16usize),
                    (2012217345u32, 99usize),
                    (1996488705u32, 100usize),
                    (1744830465u32, 101usize),
                    (1048576u32, 26usize),
                    (2012217345u32, 111usize),
                    (1996488705u32, 112usize),
                    (1744830465u32, 113usize),
                    (1048576u32, 39usize),
                    (2012217345u32, 123usize),
                    (1996488705u32, 124usize),
                    (1744830465u32, 125usize),
                    (1048576u32, 52usize),
                    (2012217345u32, 135usize),
                    (1996488705u32, 136usize),
                    (1744830465u32, 137usize),
                    (1048576u32, 65usize),
                    (2012217345u32, 147usize),
                    (1996488705u32, 148usize),
                    (1744830465u32, 149usize),
                    (1048576u32, 81usize),
                    (2012217345u32, 159usize),
                    (1996488705u32, 160usize),
                    (1744830465u32, 161usize),
                    (268435454u32, 102usize),
                    (268435454u32, 114usize),
                    (268435454u32, 126usize),
                    (268435454u32, 138usize),
                    (268435454u32, 150usize),
                    (268435454u32, 162usize),
                    (268435454u32, 103usize),
                    (268435454u32, 115usize),
                    (268435454u32, 127usize),
                    (268435454u32, 139usize),
                    (268435454u32, 151usize),
                    (268435454u32, 163usize),
                    (268435454u32, 104usize),
                    (268435454u32, 116usize),
                    (268435454u32, 128usize),
                    (268435454u32, 140usize),
                    (268435454u32, 152usize),
                    (268435454u32, 164usize),
                    (1048576u32, 21usize),
                    (2012217345u32, 102usize),
                    (1996488705u32, 103usize),
                    (1744830465u32, 104usize),
                    (1048576u32, 32usize),
                    (2012217345u32, 114usize),
                    (1996488705u32, 115usize),
                    (1744830465u32, 116usize),
                    (1048576u32, 45usize),
                    (2012217345u32, 126usize),
                    (1996488705u32, 127usize),
                    (1744830465u32, 128usize),
                    (1048576u32, 58usize),
                    (2012217345u32, 138usize),
                    (1996488705u32, 139usize),
                    (1744830465u32, 140usize),
                    (1048576u32, 71usize),
                    (2012217345u32, 150usize),
                    (1996488705u32, 151usize),
                    (1744830465u32, 152usize),
                    (1048576u32, 86usize),
                    (2012217345u32, 162usize),
                    (1996488705u32, 163usize),
                    (1744830465u32, 164usize),
                    (268435454u32, 105usize),
                    (268435454u32, 117usize),
                    (268435454u32, 129usize),
                    (268435454u32, 141usize),
                    (268435454u32, 153usize),
                    (268435454u32, 165usize),
                    (268435454u32, 106usize),
                    (268435454u32, 118usize),
                    (268435454u32, 130usize),
                    (268435454u32, 142usize),
                    (268435454u32, 154usize),
                    (268435454u32, 166usize),
                    (268435454u32, 107usize),
                    (268435454u32, 119usize),
                    (268435454u32, 131usize),
                    (268435454u32, 143usize),
                    (268435454u32, 155usize),
                    (268435454u32, 167usize),
                ];
                let mut _vl = 0;
                while _vl < 21usize {
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
                const VS_DESCS: [(usize, usize, usize); 1usize] = [(255usize, 0usize, 8usize)];
                const VS_DEPS: [usize; 8usize] = [
                    185usize, 186usize, 187usize, 188usize, 189usize, 190usize, 191usize, 192usize,
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
                let cached = *state.prev_claims.get_unchecked(195usize);
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
                let cached = *state.prev_claims.get_unchecked(196usize);
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
                    let mut ts_low = *state.prev_claims.get_unchecked(89usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(90usize);
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
                let cached = *state.prev_claims.get_unchecked(197usize);
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
                    let mut ts_low = *state.prev_claims.get_unchecked(89usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(90usize);
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
                let cached = *state.prev_claims.get_unchecked(198usize);
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
                let cached = *state.prev_claims.get_unchecked(199usize);
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
                let cached = *state.prev_claims.get_unchecked(200usize);
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
                    let mut ts_low = *state.prev_claims.get_unchecked(89usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(90usize);
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
                let cached = *state.prev_claims.get_unchecked(201usize);
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
                    let mut ts_low = *state.prev_claims.get_unchecked(89usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(90usize);
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
                let cached = *state.prev_claims.get_unchecked(202usize);
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
                let cached = *state.prev_claims.get_unchecked(203usize);
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
                let cached = *state.prev_claims.get_unchecked(204usize);
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
                    let mut ts_low = *state.prev_claims.get_unchecked(89usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(90usize);
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
                let cached = *state.prev_claims.get_unchecked(205usize);
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
                    let mut ts_low = *state.prev_claims.get_unchecked(89usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(90usize);
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
                let cached = *state.prev_claims.get_unchecked(206usize);
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
                let cached = *state.prev_claims.get_unchecked(207usize);
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
                let cached = *state.prev_claims.get_unchecked(208usize);
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
                    let mut ts_low = *state.prev_claims.get_unchecked(89usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(90usize);
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
                let cached = *state.prev_claims.get_unchecked(209usize);
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
                    let mut ts_low = *state.prev_claims.get_unchecked(89usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(90usize);
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
                let cached = *state.prev_claims.get_unchecked(210usize);
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
                let cached = *state.prev_claims.get_unchecked(211usize);
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
                let cached = *state.prev_claims.get_unchecked(212usize);
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
                    let mut ts_low = *state.prev_claims.get_unchecked(89usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(90usize);
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
                let cached = *state.prev_claims.get_unchecked(213usize);
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
                    let mut ts_low = *state.prev_claims.get_unchecked(89usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(90usize);
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
                let cached = *state.prev_claims.get_unchecked(214usize);
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
                let cached = *state.prev_claims.get_unchecked(215usize);
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
                let cached = *state.prev_claims.get_unchecked(216usize);
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
                    let mut ts_low = *state.prev_claims.get_unchecked(89usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(90usize);
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
                let cached = *state.prev_claims.get_unchecked(217usize);
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
                    let mut ts_low = *state.prev_claims.get_unchecked(89usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(90usize);
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
                let cached = *state.prev_claims.get_unchecked(218usize);
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
                let cached = *state.prev_claims.get_unchecked(219usize);
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
                let cached = *state.prev_claims.get_unchecked(220usize);
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
                    let mut ts_low = *state.prev_claims.get_unchecked(89usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(90usize);
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
                let cached = *state.prev_claims.get_unchecked(221usize);
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
                    let mut ts_low = *state.prev_claims.get_unchecked(89usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(90usize);
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
                let cached = *state.prev_claims.get_unchecked(222usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 28usize));
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
                    &BabyBearField::from_reduced_raw_repr(536866652u32),
                );
                field_ops::add_assign(&mut expected, &t_addr);
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(89usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(90usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                let cached = *state.prev_claims.get_unchecked(223usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 29usize));
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
                    &BabyBearField::from_reduced_raw_repr(536866652u32),
                );
                field_ops::add_assign(&mut expected, &t_addr);
                let cached = *state.prev_claims.get_unchecked(224usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 30usize));
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
