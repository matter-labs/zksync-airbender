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
    output_claims: &[BabyBearExt4; 90usize],
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
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_0_final_step_accumulator(
    evals: &[[BabyBearExt4; 2]],
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
            (SimpleGateType::Copy, [227usize, 0usize, 0usize, 0usize]),
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
            (
                SimpleGateType::Product,
                [257usize, 258usize, 0usize, 0usize],
            ),
            (SimpleGateType::Copy, [259usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [260usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupWithSetup,
                [228usize, 173usize, 230usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [229usize, 261usize, 0usize, 0usize],
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
            (SimpleGateType::Copy, [288usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupWithSetup,
                [289usize, 174usize, 290usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [291usize, 292usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [293usize, 294usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [295usize, 296usize, 0usize, 0usize],
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
        ];
        let mut _sg = 0;
        while _sg < 54usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                SimpleGateType::Copy => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::Product => {
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
                SimpleGateType::MaskToIdentity => {
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
                SimpleGateType::UnbalancedProduct => {
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
                SimpleGateType::LookupInitialPair => {
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
                SimpleGateType::LookupWithSetup => {
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
                SimpleGateType::LookupUnbalanced => {
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
                SimpleGateType::LookupAggregatePair => {
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
                SimpleGateType::LookupInitialWithCachedDenominators => {
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
            }
            _sg += 1;
        }
    }
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(227usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(227usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(227usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 1usize] = [(176usize, 268435454usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 1usize] = [(178usize, 268435454usize)];
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
                (175usize, 1744830467usize),
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
                (227usize, 268435454usize),
                (227usize, 268435454usize),
                (227usize, 268435454usize),
                (227usize, 268435454usize),
                (227usize, 268435454usize),
                (227usize, 268435454usize),
                (227usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(227usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 5usize] = [
                (227usize, 268435454usize),
                (227usize, 268435454usize),
                (227usize, 268435454usize),
                (227usize, 268435454usize),
                (227usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(227usize, 1744830467usize)];
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
                (227usize, 1744830467usize),
                (227usize, 1744830467usize),
                (227usize, 1744830467usize),
                (227usize, 1744830467usize),
                (227usize, 1744830467usize),
                (227usize, 1744830467usize),
                (227usize, 1744830467usize),
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 5usize] = [
                (7usize, 1usize),
                (8usize, 1usize),
                (9usize, 1usize),
                (10usize, 1usize),
                (11usize, 1usize),
            ];
            const VAL_QI: [(usize, usize); 5usize] = [
                (227usize, 1744830467usize),
                (227usize, 1744830467usize),
                (227usize, 1744830467usize),
                (227usize, 1744830467usize),
                (227usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 5usize] = [
                (7usize, 268435454usize),
                (8usize, 268435454usize),
                (9usize, 268435454usize),
                (10usize, 268435454usize),
                (11usize, 268435454usize),
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
                (177usize, 1744830467usize),
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(4usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(7usize, 268435454usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(4usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(8usize, 268435454usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(4usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(9usize, 268435454usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(4usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(10usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(20usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(4usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(11usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(21usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 2usize] =
                [(22usize, 536870364usize), (23usize, 1744830467usize)];
            let val = super::common::eval_max_quadratic(
                evals,
                &VAL_QO,
                &VAL_QI,
                &VAL_LN,
                536853436usize,
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 2usize] =
                [(22usize, 536870364usize), (24usize, 1744830467usize)];
            let val = super::common::eval_max_quadratic(
                evals,
                &VAL_QO,
                &VAL_QI,
                &VAL_LN,
                671036075usize,
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 2usize] =
                [(22usize, 536870364usize), (25usize, 1744830467usize)];
            let val = super::common::eval_max_quadratic(
                evals,
                &VAL_QO,
                &VAL_QI,
                &VAL_LN,
                805218714usize,
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 2usize] =
                [(22usize, 536870364usize), (26usize, 1744830467usize)];
            let val = super::common::eval_max_quadratic(
                evals,
                &VAL_QO,
                &VAL_QI,
                &VAL_LN,
                939401353usize,
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
                (179usize, 1744830467usize),
                (1usize, 1744970275usize),
                (2usize, 1476674629usize),
                (17usize, 1744970275usize),
                (18usize, 1476674629usize),
                (19usize, 2097152usize),
                (20usize, 538688444usize),
                (21usize, 806984090usize),
                (40usize, 1744831011usize),
                (179usize, 1744830467usize),
                (2usize, 1744970275usize),
                (17usize, 1744970275usize),
                (18usize, 1476674629usize),
                (19usize, 2097152usize),
                (20usize, 538688444usize),
                (21usize, 806984090usize),
                (40usize, 1744831011usize),
                (187usize, 1744830467usize),
                (179usize, 1744830467usize),
                (179usize, 1744830467usize),
                (179usize, 1744830467usize),
                (195usize, 1744830467usize),
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
                (219usize, 1744830467usize),
                (187usize, 1744830467usize),
                (179usize, 1744830467usize),
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
                (181usize, 1744830467usize),
                (50usize, 268435454usize),
                (56usize, 1744831011usize),
                (221usize, 1744830467usize),
                (27usize, 1744830467usize),
                (50usize, 268435454usize),
                (56usize, 1744831011usize),
                (181usize, 1744830467usize),
                (181usize, 1744830467usize),
                (213usize, 1744830467usize),
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
                (180usize, 1744830467usize),
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
                (180usize, 1744830467usize),
                (2usize, 1744970275usize),
                (17usize, 1744970275usize),
                (18usize, 1476674629usize),
                (19usize, 2097152usize),
                (20usize, 538688444usize),
                (21usize, 806984090usize),
                (40usize, 268435454usize),
                (41usize, 1744830467usize),
                (42usize, 1744831011usize),
                (188usize, 1744830467usize),
                (180usize, 1744830467usize),
                (180usize, 1744830467usize),
                (180usize, 1744830467usize),
                (196usize, 1744830467usize),
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
                (220usize, 1744830467usize),
                (188usize, 1744830467usize),
                (180usize, 1744830467usize),
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
                (182usize, 1744830467usize),
                (47usize, 268435454usize),
                (56usize, 268435454usize),
                (57usize, 1744830467usize),
                (58usize, 1744831011usize),
                (222usize, 1744830467usize),
                (28usize, 1744830467usize),
                (47usize, 268435454usize),
                (56usize, 268435454usize),
                (57usize, 1744830467usize),
                (58usize, 1744831011usize),
                (182usize, 1744830467usize),
                (182usize, 1744830467usize),
                (214usize, 1744830467usize),
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
                (183usize, 1744830467usize),
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
                (183usize, 1744830467usize),
                (2usize, 1744970275usize),
                (17usize, 1744970275usize),
                (18usize, 1476674629usize),
                (19usize, 2097152usize),
                (20usize, 538688444usize),
                (21usize, 806984090usize),
                (41usize, 268435454usize),
                (43usize, 1744830467usize),
                (44usize, 1744831011usize),
                (191usize, 1744830467usize),
                (183usize, 1744830467usize),
                (183usize, 1744830467usize),
                (183usize, 1744830467usize),
                (199usize, 1744830467usize),
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
                (223usize, 1744830467usize),
                (191usize, 1744830467usize),
                (183usize, 1744830467usize),
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
                (185usize, 1744830467usize),
                (48usize, 268435454usize),
                (57usize, 268435454usize),
                (59usize, 1744830467usize),
                (60usize, 1744831011usize),
                (225usize, 1744830467usize),
                (29usize, 1744830467usize),
                (48usize, 268435454usize),
                (57usize, 268435454usize),
                (59usize, 1744830467usize),
                (60usize, 1744831011usize),
                (185usize, 1744830467usize),
                (185usize, 1744830467usize),
                (217usize, 1744830467usize),
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
                (184usize, 1744830467usize),
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
                (184usize, 1744830467usize),
                (2usize, 1744970275usize),
                (17usize, 1744970275usize),
                (18usize, 1476674629usize),
                (19usize, 2097152usize),
                (20usize, 538688444usize),
                (21usize, 806984090usize),
                (42usize, 268435454usize),
                (45usize, 1744830467usize),
                (46usize, 1744831011usize),
                (192usize, 1744830467usize),
                (184usize, 1744830467usize),
                (184usize, 1744830467usize),
                (184usize, 1744830467usize),
                (200usize, 1744830467usize),
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
                (224usize, 1744830467usize),
                (192usize, 1744830467usize),
                (184usize, 1744830467usize),
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
                (186usize, 1744830467usize),
                (49usize, 268435454usize),
                (58usize, 268435454usize),
                (61usize, 1744830467usize),
                (62usize, 1744831011usize),
                (226usize, 1744830467usize),
                (30usize, 1744830467usize),
                (49usize, 268435454usize),
                (58usize, 268435454usize),
                (61usize, 1744830467usize),
                (62usize, 1744831011usize),
                (186usize, 1744830467usize),
                (186usize, 1744830467usize),
                (218usize, 1744830467usize),
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
                (181usize, 1744830467usize),
                (1usize, 1744970275usize),
                (17usize, 671787691usize),
                (18usize, 538688444usize),
                (19usize, 135196399usize),
                (20usize, 1880166674usize),
                (21usize, 671787691usize),
                (64usize, 1744831011usize),
                (195usize, 1744830467usize),
                (211usize, 1744830467usize),
                (187usize, 1744830467usize),
                (187usize, 1744830467usize),
                (187usize, 1744830467usize),
                (187usize, 1744830467usize),
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
                (187usize, 1744830467usize),
                (71usize, 1744830467usize),
                (72usize, 1744831011usize),
                (27usize, 1744830467usize),
                (219usize, 1744830467usize),
                (195usize, 1744830467usize),
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
                (213usize, 1744830467usize),
                (189usize, 1744830467usize),
                (189usize, 1744830467usize),
                (27usize, 1744830467usize),
                (189usize, 1744830467usize),
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
                (182usize, 1744830467usize),
                (1usize, 1744970275usize),
                (17usize, 671787691usize),
                (18usize, 538688444usize),
                (19usize, 135196399usize),
                (20usize, 1880166674usize),
                (21usize, 671787691usize),
                (64usize, 268435454usize),
                (65usize, 1744830467usize),
                (66usize, 1744831011usize),
                (196usize, 1744830467usize),
                (212usize, 1744830467usize),
                (188usize, 1744830467usize),
                (188usize, 1744830467usize),
                (188usize, 1744830467usize),
                (188usize, 1744830467usize),
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
                (188usize, 1744830467usize),
                (73usize, 1744830467usize),
                (74usize, 1744831011usize),
                (28usize, 1744830467usize),
                (220usize, 1744830467usize),
                (196usize, 1744830467usize),
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
                (214usize, 1744830467usize),
                (190usize, 1744830467usize),
                (190usize, 1744830467usize),
                (28usize, 1744830467usize),
                (190usize, 1744830467usize),
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
                (185usize, 1744830467usize),
                (1usize, 1744970275usize),
                (17usize, 671787691usize),
                (18usize, 538688444usize),
                (19usize, 135196399usize),
                (20usize, 1880166674usize),
                (21usize, 671787691usize),
                (65usize, 268435454usize),
                (67usize, 1744830467usize),
                (68usize, 1744831011usize),
                (199usize, 1744830467usize),
                (215usize, 1744830467usize),
                (191usize, 1744830467usize),
                (191usize, 1744830467usize),
                (191usize, 1744830467usize),
                (191usize, 1744830467usize),
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
                (191usize, 1744830467usize),
                (75usize, 1744830467usize),
                (76usize, 1744831011usize),
                (29usize, 1744830467usize),
                (223usize, 1744830467usize),
                (199usize, 1744830467usize),
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
                (217usize, 1744830467usize),
                (193usize, 1744830467usize),
                (193usize, 1744830467usize),
                (29usize, 1744830467usize),
                (193usize, 1744830467usize),
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
                (186usize, 1744830467usize),
                (1usize, 1744970275usize),
                (17usize, 671787691usize),
                (18usize, 538688444usize),
                (19usize, 135196399usize),
                (20usize, 1880166674usize),
                (21usize, 671787691usize),
                (66usize, 268435454usize),
                (69usize, 1744830467usize),
                (70usize, 1744831011usize),
                (200usize, 1744830467usize),
                (216usize, 1744830467usize),
                (192usize, 1744830467usize),
                (192usize, 1744830467usize),
                (192usize, 1744830467usize),
                (192usize, 1744830467usize),
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
                (192usize, 1744830467usize),
                (77usize, 1744830467usize),
                (78usize, 1744831011usize),
                (30usize, 1744830467usize),
                (224usize, 1744830467usize),
                (200usize, 1744830467usize),
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
                (218usize, 1744830467usize),
                (194usize, 1744830467usize),
                (194usize, 1744830467usize),
                (30usize, 1744830467usize),
                (194usize, 1744830467usize),
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
                (179usize, 1744830467usize),
                (2usize, 1744970275usize),
                (17usize, 940083337usize),
                (18usize, 1075279736usize),
                (19usize, 806984090usize),
                (20usize, 1343575382usize),
                (21usize, 1880166674usize),
                (88usize, 1744831011usize),
                (203usize, 1744830467usize),
                (195usize, 1744830467usize),
                (195usize, 1744830467usize),
                (179usize, 1744830467usize),
                (179usize, 1744830467usize),
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
                (195usize, 1744830467usize),
                (27usize, 1744830467usize),
                (95usize, 1744830467usize),
                (96usize, 1744831011usize),
                (219usize, 1744830467usize),
                (27usize, 1744830467usize),
                (211usize, 1744830467usize),
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
                (181usize, 1744830467usize),
                (31usize, 1744830467usize),
                (98usize, 268435454usize),
                (104usize, 1744831011usize),
                (197usize, 1744830467usize),
                (197usize, 1744830467usize),
                (181usize, 1744830467usize),
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
                (180usize, 1744830467usize),
                (2usize, 1744970275usize),
                (17usize, 940083337usize),
                (18usize, 1075279736usize),
                (19usize, 806984090usize),
                (20usize, 1343575382usize),
                (21usize, 1880166674usize),
                (88usize, 268435454usize),
                (89usize, 1744830467usize),
                (90usize, 1744831011usize),
                (204usize, 1744830467usize),
                (196usize, 1744830467usize),
                (196usize, 1744830467usize),
                (180usize, 1744830467usize),
                (180usize, 1744830467usize),
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
                (196usize, 1744830467usize),
                (28usize, 1744830467usize),
                (97usize, 1744830467usize),
                (98usize, 1744831011usize),
                (220usize, 1744830467usize),
                (28usize, 1744830467usize),
                (212usize, 1744830467usize),
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
                (182usize, 1744830467usize),
                (32usize, 1744830467usize),
                (95usize, 268435454usize),
                (104usize, 268435454usize),
                (105usize, 1744830467usize),
                (106usize, 1744831011usize),
                (198usize, 1744830467usize),
                (198usize, 1744830467usize),
                (182usize, 1744830467usize),
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
                (183usize, 1744830467usize),
                (2usize, 1744970275usize),
                (17usize, 940083337usize),
                (18usize, 1075279736usize),
                (19usize, 806984090usize),
                (20usize, 1343575382usize),
                (21usize, 1880166674usize),
                (89usize, 268435454usize),
                (91usize, 1744830467usize),
                (92usize, 1744831011usize),
                (207usize, 1744830467usize),
                (199usize, 1744830467usize),
                (199usize, 1744830467usize),
                (183usize, 1744830467usize),
                (183usize, 1744830467usize),
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
                (199usize, 1744830467usize),
                (29usize, 1744830467usize),
                (99usize, 1744830467usize),
                (100usize, 1744831011usize),
                (223usize, 1744830467usize),
                (29usize, 1744830467usize),
                (215usize, 1744830467usize),
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
                (185usize, 1744830467usize),
                (33usize, 1744830467usize),
                (96usize, 268435454usize),
                (105usize, 268435454usize),
                (107usize, 1744830467usize),
                (108usize, 1744831011usize),
                (201usize, 1744830467usize),
                (201usize, 1744830467usize),
                (185usize, 1744830467usize),
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
                (184usize, 1744830467usize),
                (2usize, 1744970275usize),
                (17usize, 940083337usize),
                (18usize, 1075279736usize),
                (19usize, 806984090usize),
                (20usize, 1343575382usize),
                (21usize, 1880166674usize),
                (90usize, 268435454usize),
                (93usize, 1744830467usize),
                (94usize, 1744831011usize),
                (208usize, 1744830467usize),
                (200usize, 1744830467usize),
                (200usize, 1744830467usize),
                (184usize, 1744830467usize),
                (184usize, 1744830467usize),
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
                (200usize, 1744830467usize),
                (30usize, 1744830467usize),
                (101usize, 1744830467usize),
                (102usize, 1744831011usize),
                (224usize, 1744830467usize),
                (30usize, 1744830467usize),
                (216usize, 1744830467usize),
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
                (186usize, 1744830467usize),
                (34usize, 1744830467usize),
                (97usize, 268435454usize),
                (106usize, 268435454usize),
                (109usize, 1744830467usize),
                (110usize, 1744831011usize),
                (202usize, 1744830467usize),
                (202usize, 1744830467usize),
                (186usize, 1744830467usize),
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
                (211usize, 1744830467usize),
                (187usize, 1744830467usize),
                (203usize, 1744830467usize),
                (203usize, 1744830467usize),
                (195usize, 1744830467usize),
                (195usize, 1744830467usize),
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
                (203usize, 1744830467usize),
                (119usize, 1744830467usize),
                (120usize, 1744831011usize),
                (31usize, 1744830467usize),
                (219usize, 1744830467usize),
                (203usize, 1744830467usize),
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
                (189usize, 1744830467usize),
                (205usize, 1744830467usize),
                (205usize, 1744830467usize),
                (31usize, 1744830467usize),
                (197usize, 1744830467usize),
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
                (212usize, 1744830467usize),
                (188usize, 1744830467usize),
                (204usize, 1744830467usize),
                (204usize, 1744830467usize),
                (196usize, 1744830467usize),
                (196usize, 1744830467usize),
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
                (204usize, 1744830467usize),
                (121usize, 1744830467usize),
                (122usize, 1744831011usize),
                (32usize, 1744830467usize),
                (220usize, 1744830467usize),
                (204usize, 1744830467usize),
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
                (190usize, 1744830467usize),
                (206usize, 1744830467usize),
                (206usize, 1744830467usize),
                (32usize, 1744830467usize),
                (198usize, 1744830467usize),
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
                (215usize, 1744830467usize),
                (191usize, 1744830467usize),
                (207usize, 1744830467usize),
                (207usize, 1744830467usize),
                (199usize, 1744830467usize),
                (199usize, 1744830467usize),
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
                (123usize, 1744830467usize),
                (124usize, 1744831011usize),
                (33usize, 1744830467usize),
                (223usize, 1744830467usize),
                (207usize, 1744830467usize),
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
                (193usize, 1744830467usize),
                (209usize, 1744830467usize),
                (209usize, 1744830467usize),
                (33usize, 1744830467usize),
                (201usize, 1744830467usize),
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
                (216usize, 1744830467usize),
                (192usize, 1744830467usize),
                (208usize, 1744830467usize),
                (208usize, 1744830467usize),
                (200usize, 1744830467usize),
                (200usize, 1744830467usize),
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
                (125usize, 1744830467usize),
                (126usize, 1744831011usize),
                (34usize, 1744830467usize),
                (224usize, 1744830467usize),
                (208usize, 1744830467usize),
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
                (194usize, 1744830467usize),
                (210usize, 1744830467usize),
                (210usize, 1744830467usize),
                (34usize, 1744830467usize),
                (202usize, 1744830467usize),
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
                (195usize, 1744830467usize),
                (203usize, 1744830467usize),
                (211usize, 1744830467usize),
                (211usize, 1744830467usize),
                (187usize, 1744830467usize),
                (179usize, 1744830467usize),
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
                (211usize, 1744830467usize),
                (31usize, 1744830467usize),
                (219usize, 1744830467usize),
                (219usize, 1744830467usize),
                (31usize, 1744830467usize),
                (203usize, 1744830467usize),
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
                (221usize, 1744830467usize),
                (197usize, 1744830467usize),
                (205usize, 1744830467usize),
                (213usize, 1744830467usize),
                (213usize, 1744830467usize),
                (189usize, 1744830467usize),
                (181usize, 1744830467usize),
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
                (196usize, 1744830467usize),
                (204usize, 1744830467usize),
                (212usize, 1744830467usize),
                (212usize, 1744830467usize),
                (188usize, 1744830467usize),
                (180usize, 1744830467usize),
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
                (212usize, 1744830467usize),
                (32usize, 1744830467usize),
                (220usize, 1744830467usize),
                (220usize, 1744830467usize),
                (32usize, 1744830467usize),
                (204usize, 1744830467usize),
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
                (222usize, 1744830467usize),
                (198usize, 1744830467usize),
                (206usize, 1744830467usize),
                (214usize, 1744830467usize),
                (214usize, 1744830467usize),
                (190usize, 1744830467usize),
                (182usize, 1744830467usize),
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
                (199usize, 1744830467usize),
                (207usize, 1744830467usize),
                (215usize, 1744830467usize),
                (215usize, 1744830467usize),
                (191usize, 1744830467usize),
                (183usize, 1744830467usize),
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
                (215usize, 1744830467usize),
                (33usize, 1744830467usize),
                (223usize, 1744830467usize),
                (223usize, 1744830467usize),
                (33usize, 1744830467usize),
                (207usize, 1744830467usize),
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
                (225usize, 1744830467usize),
                (201usize, 1744830467usize),
                (209usize, 1744830467usize),
                (217usize, 1744830467usize),
                (217usize, 1744830467usize),
                (193usize, 1744830467usize),
                (185usize, 1744830467usize),
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
                (200usize, 1744830467usize),
                (208usize, 1744830467usize),
                (216usize, 1744830467usize),
                (216usize, 1744830467usize),
                (192usize, 1744830467usize),
                (184usize, 1744830467usize),
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
                (216usize, 1744830467usize),
                (34usize, 1744830467usize),
                (224usize, 1744830467usize),
                (224usize, 1744830467usize),
                (34usize, 1744830467usize),
                (208usize, 1744830467usize),
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
                (226usize, 1744830467usize),
                (202usize, 1744830467usize),
                (210usize, 1744830467usize),
                (218usize, 1744830467usize),
                (218usize, 1744830467usize),
                (194usize, 1744830467usize),
                (186usize, 1744830467usize),
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(187usize, 268435454usize), (189usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(188usize, 268435454usize), (190usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(191usize, 268435454usize), (193usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(192usize, 268435454usize), (194usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(195usize, 268435454usize), (197usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(196usize, 268435454usize), (198usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(199usize, 268435454usize), (201usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(200usize, 268435454usize), (202usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(203usize, 268435454usize), (205usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(204usize, 268435454usize), (206usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(207usize, 268435454usize), (209usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(208usize, 268435454usize), (210usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(211usize, 268435454usize), (213usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(212usize, 268435454usize), (214usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(215usize, 268435454usize), (217usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(0usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(216usize, 268435454usize), (218usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(187usize, 268435454usize), (189usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(188usize, 268435454usize), (190usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(191usize, 268435454usize), (193usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(192usize, 268435454usize), (194usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(203usize, 268435454usize), (205usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(204usize, 268435454usize), (206usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(207usize, 268435454usize), (209usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(208usize, 268435454usize), (210usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(211usize, 268435454usize), (213usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(212usize, 268435454usize), (214usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(215usize, 268435454usize), (217usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(1usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(216usize, 268435454usize), (218usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(179usize, 268435454usize), (181usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(180usize, 268435454usize), (182usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(183usize, 268435454usize), (185usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(184usize, 268435454usize), (186usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(195usize, 268435454usize), (197usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(196usize, 268435454usize), (198usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(199usize, 268435454usize), (201usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(200usize, 268435454usize), (202usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(219usize, 268435454usize), (221usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(220usize, 268435454usize), (222usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(223usize, 268435454usize), (225usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(224usize, 268435454usize), (226usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(219usize, 268435454usize), (221usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(220usize, 268435454usize), (222usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(223usize, 268435454usize), (225usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(224usize, 268435454usize), (226usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(4usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(219usize, 268435454usize), (221usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(4usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(220usize, 268435454usize), (222usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(4usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(223usize, 268435454usize), (225usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(4usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(224usize, 268435454usize), (226usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(179usize, 268435454usize), (221usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(180usize, 268435454usize), (222usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(183usize, 268435454usize), (225usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(184usize, 268435454usize), (226usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(195usize, 268435454usize), (197usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(196usize, 268435454usize), (198usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(199usize, 268435454usize), (201usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(200usize, 268435454usize), (202usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(203usize, 268435454usize), (205usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(204usize, 268435454usize), (206usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(207usize, 268435454usize), (209usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(5usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(208usize, 268435454usize), (210usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(203usize, 268435454usize), (205usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(204usize, 268435454usize), (206usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(207usize, 268435454usize), (209usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(208usize, 268435454usize), (210usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(211usize, 268435454usize), (213usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(212usize, 268435454usize), (214usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(215usize, 268435454usize), (217usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(216usize, 268435454usize), (218usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(219usize, 268435454usize), (221usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(220usize, 268435454usize), (222usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(223usize, 268435454usize), (225usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(6usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(224usize, 268435454usize), (226usize, 1744830467usize)];
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(10usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(10usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(10usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(11usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(11usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(11usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(12usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(12usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(12usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(13usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(13usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(14usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(14usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(14usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(15usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(15usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(15usize, 1744830467usize)];
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
        for j in 0..2 {
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(159usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(159usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(159usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(160usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(160usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(160usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(161usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(161usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(161usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(162usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(162usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(162usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(163usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(163usize, 268435454usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(164usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(164usize, 268435454usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(165usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(165usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(165usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(166usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(166usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(166usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(167usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(167usize, 268435454usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(168usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(168usize, 268435454usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(169usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(169usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(169usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(170usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(170usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(170usize, 1744830467usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(171usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(171usize, 268435454usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(172usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(172usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(172usize, 1744830467usize)];
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
    output_claims: &[BabyBearExt4; 47usize],
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
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_1_final_step_accumulator(
    evals: &[[BabyBearExt4; 2]],
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 29usize] = [
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
                [45usize, 46usize, 47usize, 0usize],
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
                SimpleGateType::LookupAggregatePair,
                [19usize, 20usize, 17usize, 18usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [88usize, 89usize, 86usize, 87usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [84usize, 85usize, 82usize, 83usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [80usize, 81usize, 78usize, 79usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [76usize, 77usize, 74usize, 75usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [72usize, 73usize, 70usize, 71usize],
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
            (SimpleGateType::Copy, [48usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [49usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 29usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                SimpleGateType::Copy => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::Product => {
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
                SimpleGateType::MaskToIdentity => {
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
                SimpleGateType::UnbalancedProduct => {
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
                SimpleGateType::LookupInitialPair => {
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
                SimpleGateType::LookupWithSetup => {
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
                SimpleGateType::LookupUnbalanced => {
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
                SimpleGateType::LookupAggregatePair => {
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
                SimpleGateType::LookupInitialWithCachedDenominators => {
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
            }
            _sg += 1;
        }
    }
    acc
}
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_2_compute_claim(
    output_claims: &[BabyBearExt4; 25usize],
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
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_2_final_step_accumulator(
    evals: &[[BabyBearExt4; 2]],
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 16usize] = [
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
            (SimpleGateType::Copy, [25usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [26usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 16usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                SimpleGateType::Copy => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::Product => {
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
                SimpleGateType::MaskToIdentity => {
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
                SimpleGateType::UnbalancedProduct => {
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
                SimpleGateType::LookupInitialPair => {
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
                SimpleGateType::LookupWithSetup => {
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
                SimpleGateType::LookupUnbalanced => {
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
                SimpleGateType::LookupAggregatePair => {
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
                SimpleGateType::LookupInitialWithCachedDenominators => {
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
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_3_final_step_accumulator(
    evals: &[[BabyBearExt4; 2]],
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 8usize] = [
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
        ];
        let mut _sg = 0;
        while _sg < 8usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                SimpleGateType::Copy => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::Product => {
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
                SimpleGateType::MaskToIdentity => {
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
                SimpleGateType::UnbalancedProduct => {
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
                SimpleGateType::LookupInitialPair => {
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
                SimpleGateType::LookupWithSetup => {
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
                SimpleGateType::LookupUnbalanced => {
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
                SimpleGateType::LookupAggregatePair => {
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
                SimpleGateType::LookupInitialWithCachedDenominators => {
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
    evals: &[[BabyBearExt4; 2]],
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
                [11usize, 12usize, 9usize, 10usize],
            ),
            (SimpleGateType::Copy, [7usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [8usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 6usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                SimpleGateType::Copy => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::Product => {
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
                SimpleGateType::MaskToIdentity => {
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
                SimpleGateType::UnbalancedProduct => {
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
                SimpleGateType::LookupInitialPair => {
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
                SimpleGateType::LookupWithSetup => {
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
                SimpleGateType::LookupUnbalanced => {
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
                SimpleGateType::LookupAggregatePair => {
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
                SimpleGateType::LookupInitialWithCachedDenominators => {
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
            }
            _sg += 1;
        }
    }
    acc
}
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_5_compute_claim(
    output_claims: &[BabyBearExt4; 6usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 5usize] = [
        (2usize, 0usize, 1usize),
        (1usize, 2usize, 0usize),
        (1usize, 3usize, 0usize),
        (1usize, 4usize, 0usize),
        (1usize, 5usize, 0usize),
    ];
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_5_final_step_accumulator(
    evals: &[[BabyBearExt4; 2]],
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
                SimpleGateType::LookupAggregatePair,
                [6usize, 7usize, 4usize, 5usize],
            ),
            (SimpleGateType::Copy, [0usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [1usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [2usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [3usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 5usize {
            let (gt, idx) = unsafe { *SIMPLE_GATES.get_unchecked(_sg) };
            match gt {
                SimpleGateType::Copy => {
                    let bc = current_batch;
                    field_ops::mul_assign(&mut current_batch, &batch_base);
                    for j in 0..2 {
                        let val = evals.get_unchecked(idx[0])[j];
                        let mut contrib = bc;
                        field_ops::mul_assign(&mut contrib, &val);
                        field_ops::add_assign(&mut acc[j], &contrib);
                    }
                }
                SimpleGateType::Product => {
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
                SimpleGateType::MaskToIdentity => {
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
                SimpleGateType::UnbalancedProduct => {
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
                SimpleGateType::LookupInitialPair => {
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
                SimpleGateType::LookupWithSetup => {
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
                SimpleGateType::LookupUnbalanced => {
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
                SimpleGateType::LookupAggregatePair => {
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
                SimpleGateType::LookupInitialWithCachedDenominators => {
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
        if result != *state.prev_claims.get_unchecked(274usize) {
            return Err(E::gkr_virtual_setup_eval_mismatch(274usize));
        }
    }
    Ok(())
}
#[allow(unused_variables, unused_mut, unused_unsafe)]
pub(crate) fn verify_gkr<I: NonDeterminismSource, E: ErrorCreator>(
    external_challenges: &GKRExternalChallenges<BabyBearField, BabyBearExt4>,
    initial_transcript: &ConcreteInitialTranscript,
    ts: &mut ::verifier_common::structs::TranscriptState,
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
        #[cfg(feature = "verifier_stats")]
        verifier_common::stats::log("GKR COMPRESSION INIT");
        {
            let initial_claim = dim_reducing_compute_claim(
                state.prev_claims.as_array::<6usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 3usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    23usize,
                )?;
            let mut fc_len = 3usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 23");
        }
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
                )?;
            let mut fc_len = 4usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
                )?;
            let mut fc_len = 5usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
                )?;
            let mut fc_len = 6usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
                )?;
            let mut fc_len = 7usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
                )?;
            let mut fc_len = 8usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
                )?;
            let mut fc_len = 9usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
                )?;
            let mut fc_len = 10usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
                )?;
            let mut fc_len = 11usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
                )?;
            let mut fc_len = 12usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
                )?;
            let mut fc_len = 13usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
                )?;
            let mut fc_len = 14usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
                )?;
            let mut fc_len = 15usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
                )?;
            let mut fc_len = 16usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
                )?;
            let mut fc_len = 17usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
                )?;
            let mut fc_len = 18usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
                )?;
            let mut fc_len = 19usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
                )?;
            let mut fc_len = 20usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR COMPRESSION LAYER 6");
        }
        {
            let initial_claim = layer_5_compute_claim(
                state.prev_claims.as_array::<6usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 21usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    5usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 8usize * 2 * EXT_DEGREE;
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
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR MAIN LAYER 5");
        }
        {
            let initial_claim = layer_4_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 21usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    4usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 13usize * 2 * EXT_DEGREE;
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
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR MAIN LAYER 4");
        }
        {
            let initial_claim = layer_3_compute_claim(
                state.prev_claims.as_array::<13usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 21usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    3usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 25usize * 2 * EXT_DEGREE;
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
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR MAIN LAYER 3");
        }
        {
            let initial_claim = layer_2_compute_claim(
                state.prev_claims.as_array::<25usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 21usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    2usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 47usize * 2 * EXT_DEGREE;
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
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR MAIN LAYER 2");
        }
        {
            let initial_claim = layer_1_compute_claim(
                state.prev_claims.as_array::<47usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 21usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    1usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 90usize * 2 * EXT_DEGREE;
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
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR MAIN LAYER 1");
        }
        {
            let initial_claim = layer_0_compute_claim(
                state.prev_claims.as_array::<90usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 21usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    0usize,
                )?;
            let mut fc_len = 21usize;
            let data_words = 331usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(331usize);
                let f = layer_0_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
            let last_r = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = last_r;
            fc_len += 1;
            const EXTRA_COMMIT_BUF: usize = {
                let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + 44usize * EXT_DEGREE;
                total.div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS) * BLAKE2S_BLOCK_SIZE_U32_WORDS
            };
            let mut extra_buf = CommitBuf::<EXTRA_COMMIT_BUF>::new();
            let extra_data_words = 44usize * EXT_DEGREE;
            {
                let mut i = 0;
                while i < extra_data_words {
                    extra_buf.data_write(i, read_reduced_field_el::<I>());
                    i += 1;
                }
            }
            let mut extra_evals = LazyVec::<BabyBearExt4, 44usize>::new();
            {
                let slice: &[BabyBearExt4] = unsafe { extra_buf.data_as(44usize) };
                for el in slice {
                    extra_evals.push(*el);
                }
            }
            ts.commit(&mut extra_buf, extra_data_words);
            let final_step_evals: &[[BabyBearExt4; 2]] = unsafe { eval_buf.data_as(331usize) };
            state.prev_claims.clear();
            {
                const LAYOUT_KIND: [usize; 375usize] = [
                    1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 0usize, 0usize, 1usize, 0usize, 0usize, 1usize, 1usize, 0usize,
                    0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 1usize, 0usize, 0usize,
                    1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    1usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize,
                    1usize, 0usize, 0usize, 1usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 1usize, 0usize, 0usize, 1usize,
                    1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 1usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
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
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize,
                ];
                const LAYOUT_POS: [usize; 375usize] = [
                    0usize, 1usize, 175usize, 176usize, 177usize, 178usize, 2usize, 3usize, 4usize,
                    5usize, 6usize, 7usize, 179usize, 180usize, 8usize, 181usize, 182usize, 9usize,
                    10usize, 183usize, 184usize, 185usize, 186usize, 11usize, 12usize, 187usize,
                    188usize, 13usize, 189usize, 190usize, 14usize, 15usize, 191usize, 192usize,
                    193usize, 194usize, 16usize, 17usize, 195usize, 196usize, 18usize, 197usize,
                    198usize, 19usize, 20usize, 199usize, 200usize, 201usize, 202usize, 21usize,
                    22usize, 203usize, 204usize, 23usize, 205usize, 206usize, 24usize, 25usize,
                    207usize, 208usize, 209usize, 210usize, 26usize, 27usize, 211usize, 212usize,
                    28usize, 213usize, 214usize, 29usize, 30usize, 215usize, 216usize, 217usize,
                    218usize, 31usize, 32usize, 219usize, 220usize, 33usize, 221usize, 222usize,
                    34usize, 35usize, 223usize, 224usize, 225usize, 226usize, 227usize, 228usize,
                    229usize, 0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
                    8usize, 9usize, 10usize, 11usize, 12usize, 13usize, 14usize, 15usize, 16usize,
                    17usize, 18usize, 19usize, 20usize, 21usize, 22usize, 23usize, 24usize,
                    25usize, 26usize, 27usize, 28usize, 29usize, 30usize, 31usize, 32usize,
                    33usize, 34usize, 35usize, 36usize, 37usize, 38usize, 39usize, 40usize,
                    41usize, 42usize, 43usize, 44usize, 45usize, 46usize, 47usize, 48usize,
                    49usize, 50usize, 51usize, 52usize, 53usize, 54usize, 55usize, 56usize,
                    57usize, 58usize, 59usize, 60usize, 61usize, 62usize, 63usize, 64usize,
                    65usize, 66usize, 67usize, 68usize, 69usize, 70usize, 71usize, 72usize,
                    73usize, 74usize, 75usize, 76usize, 77usize, 78usize, 79usize, 80usize,
                    81usize, 82usize, 83usize, 84usize, 85usize, 86usize, 87usize, 88usize,
                    89usize, 90usize, 91usize, 92usize, 93usize, 94usize, 95usize, 96usize,
                    97usize, 98usize, 99usize, 100usize, 101usize, 102usize, 103usize, 104usize,
                    105usize, 106usize, 107usize, 108usize, 109usize, 110usize, 111usize, 112usize,
                    113usize, 114usize, 115usize, 116usize, 117usize, 118usize, 119usize, 120usize,
                    121usize, 122usize, 123usize, 124usize, 125usize, 126usize, 127usize, 128usize,
                    129usize, 130usize, 131usize, 132usize, 133usize, 134usize, 135usize, 136usize,
                    137usize, 138usize, 139usize, 140usize, 141usize, 142usize, 143usize, 144usize,
                    145usize, 146usize, 147usize, 148usize, 149usize, 150usize, 151usize, 152usize,
                    153usize, 154usize, 155usize, 156usize, 157usize, 158usize, 159usize, 160usize,
                    161usize, 162usize, 163usize, 164usize, 165usize, 166usize, 167usize, 168usize,
                    169usize, 170usize, 171usize, 172usize, 173usize, 174usize, 36usize, 37usize,
                    38usize, 39usize, 40usize, 41usize, 42usize, 43usize, 230usize, 231usize,
                    232usize, 233usize, 234usize, 235usize, 236usize, 237usize, 238usize, 239usize,
                    240usize, 241usize, 242usize, 243usize, 244usize, 245usize, 246usize, 247usize,
                    248usize, 249usize, 250usize, 251usize, 252usize, 253usize, 254usize, 255usize,
                    256usize, 257usize, 258usize, 259usize, 260usize, 261usize, 262usize, 263usize,
                    264usize, 265usize, 266usize, 267usize, 268usize, 269usize, 270usize, 271usize,
                    272usize, 273usize, 274usize, 275usize, 276usize, 277usize, 278usize, 279usize,
                    280usize, 281usize, 282usize, 283usize, 284usize, 285usize, 286usize, 287usize,
                    288usize, 289usize, 290usize, 291usize, 292usize, 293usize, 294usize, 295usize,
                    296usize, 297usize, 298usize, 299usize, 300usize, 301usize, 302usize, 303usize,
                    304usize, 305usize, 306usize, 307usize, 308usize, 309usize, 310usize, 311usize,
                    312usize, 313usize, 314usize, 315usize, 316usize, 317usize, 318usize, 319usize,
                    320usize, 321usize, 322usize, 323usize, 324usize, 325usize, 326usize, 327usize,
                    328usize, 329usize, 330usize,
                ];
                let mut i = 0usize;
                while i < 375usize {
                    let kind = unsafe { *LAYOUT_KIND.get_unchecked(i) };
                    let pos = unsafe { *LAYOUT_POS.get_unchecked(i) };
                    let claim: BabyBearExt4 = if kind == 0usize {
                        let ev = unsafe { final_step_evals.get_unchecked(pos) };
                        let f0 = ev[0];
                        let mut diff = ev[1];
                        field_ops::sub_assign(&mut diff, &f0);
                        field_ops::mul_assign(&mut diff, &last_r);
                        field_ops::add_assign(&mut diff, &f0);
                        diff
                    } else {
                        *extra_evals.get(pos)
                    };
                    state.prev_claims.push(claim);
                    i += 1;
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
                    (1744830467u32, 89usize),
                    (268435454u32, 0usize),
                    (133099247u32, 250usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 1usize),
                    (1744830467u32, 250usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 6usize),
                    (133099247u32, 251usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 7usize),
                    (1744830467u32, 251usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 10usize),
                    (133099247u32, 252usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 11usize),
                    (1744830467u32, 252usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 17usize),
                    (133099247u32, 253usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 18usize),
                    (1744830467u32, 253usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 23usize),
                    (133099247u32, 254usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 24usize),
                    (1744830467u32, 254usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 30usize),
                    (133099247u32, 255usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 31usize),
                    (1744830467u32, 255usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 36usize),
                    (133099247u32, 256usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 37usize),
                    (1744830467u32, 256usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 43usize),
                    (133099247u32, 257usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 44usize),
                    (1744830467u32, 257usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 49usize),
                    (133099247u32, 258usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 50usize),
                    (1744830467u32, 258usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 56usize),
                    (133099247u32, 259usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 57usize),
                    (1744830467u32, 259usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 62usize),
                    (133099247u32, 260usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 63usize),
                    (1744830467u32, 260usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 69usize),
                    (133099247u32, 261usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 70usize),
                    (1744830467u32, 261usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 75usize),
                    (133099247u32, 262usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 76usize),
                    (1744830467u32, 262usize),
                    (1744830467u32, 89usize),
                    (268435454u32, 82usize),
                    (133099247u32, 263usize),
                    (1744830467u32, 90usize),
                    (268435454u32, 83usize),
                    (1744830467u32, 263usize),
                ];
                let mut _sc = 0;
                while _sc < 28usize {
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
                    (134213359u32, 88usize),
                    (268435454u32, 2usize),
                    (268435454u32, 14usize),
                    (268435454u32, 27usize),
                    (268435454u32, 40usize),
                    (268435454u32, 53usize),
                    (268435454u32, 66usize),
                    (268435454u32, 79usize),
                    (268435454u32, 130usize),
                    (268435454u32, 138usize),
                    (268435454u32, 146usize),
                    (134217647u32, 91usize),
                    (671088555u32, 92usize),
                    (671088555u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (402653101u32, 97usize),
                    (268435454u32, 131usize),
                    (268435454u32, 139usize),
                    (268435454u32, 147usize),
                    (134217647u32, 91usize),
                    (671088555u32, 92usize),
                    (671088555u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (402653101u32, 97usize),
                    (268435454u32, 132usize),
                    (268435454u32, 140usize),
                    (268435454u32, 148usize),
                    (134217647u32, 91usize),
                    (671088555u32, 92usize),
                    (671088555u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (402653101u32, 97usize),
                    (268435454u32, 133usize),
                    (268435454u32, 141usize),
                    (268435454u32, 149usize),
                    (134217647u32, 91usize),
                    (671088555u32, 92usize),
                    (671088555u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (402653101u32, 97usize),
                    (268435454u32, 134usize),
                    (268435454u32, 142usize),
                    (268435454u32, 150usize),
                    (134217647u32, 91usize),
                    (671088555u32, 92usize),
                    (671088555u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (402653101u32, 97usize),
                    (268435454u32, 135usize),
                    (268435454u32, 143usize),
                    (268435454u32, 151usize),
                    (134217647u32, 91usize),
                    (671088555u32, 92usize),
                    (671088555u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (402653101u32, 97usize),
                    (268435454u32, 136usize),
                    (268435454u32, 144usize),
                    (268435454u32, 152usize),
                    (134217647u32, 91usize),
                    (671088555u32, 92usize),
                    (671088555u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (402653101u32, 97usize),
                    (268435454u32, 137usize),
                    (268435454u32, 145usize),
                    (268435454u32, 153usize),
                    (134217647u32, 91usize),
                    (671088555u32, 92usize),
                    (671088555u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (402653101u32, 97usize),
                    (268435454u32, 154usize),
                    (268435454u32, 162usize),
                    (268435454u32, 170usize),
                    (1073741816u32, 91usize),
                    (671088555u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 155usize),
                    (268435454u32, 163usize),
                    (268435454u32, 171usize),
                    (1073741816u32, 91usize),
                    (671088555u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 156usize),
                    (268435454u32, 164usize),
                    (268435454u32, 172usize),
                    (1073741816u32, 91usize),
                    (671088555u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 157usize),
                    (268435454u32, 165usize),
                    (268435454u32, 173usize),
                    (1073741816u32, 91usize),
                    (671088555u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 158usize),
                    (268435454u32, 166usize),
                    (268435454u32, 174usize),
                    (1073741816u32, 91usize),
                    (671088555u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 159usize),
                    (268435454u32, 167usize),
                    (268435454u32, 175usize),
                    (1073741816u32, 91usize),
                    (671088555u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 160usize),
                    (268435454u32, 168usize),
                    (268435454u32, 176usize),
                    (1073741816u32, 91usize),
                    (671088555u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 161usize),
                    (268435454u32, 169usize),
                    (268435454u32, 177usize),
                    (1073741816u32, 91usize),
                    (671088555u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 178usize),
                    (268435454u32, 186usize),
                    (268435454u32, 194usize),
                    (1073741816u32, 91usize),
                    (1073741816u32, 92usize),
                    (671088555u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (1073741816u32, 96usize),
                    (402653101u32, 97usize),
                    (268435454u32, 179usize),
                    (268435454u32, 187usize),
                    (268435454u32, 195usize),
                    (1073741816u32, 91usize),
                    (1073741816u32, 92usize),
                    (671088555u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (1073741816u32, 96usize),
                    (402653101u32, 97usize),
                    (268435454u32, 180usize),
                    (268435454u32, 188usize),
                    (268435454u32, 196usize),
                    (1073741816u32, 91usize),
                    (1073741816u32, 92usize),
                    (671088555u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (1073741816u32, 96usize),
                    (402653101u32, 97usize),
                    (268435454u32, 181usize),
                    (268435454u32, 189usize),
                    (268435454u32, 197usize),
                    (1073741816u32, 91usize),
                    (1073741816u32, 92usize),
                    (671088555u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (1073741816u32, 96usize),
                    (402653101u32, 97usize),
                    (268435454u32, 182usize),
                    (268435454u32, 190usize),
                    (268435454u32, 198usize),
                    (1073741816u32, 91usize),
                    (1073741816u32, 92usize),
                    (671088555u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (1073741816u32, 96usize),
                    (402653101u32, 97usize),
                    (268435454u32, 183usize),
                    (268435454u32, 191usize),
                    (268435454u32, 199usize),
                    (1073741816u32, 91usize),
                    (1073741816u32, 92usize),
                    (671088555u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (1073741816u32, 96usize),
                    (402653101u32, 97usize),
                    (268435454u32, 184usize),
                    (268435454u32, 192usize),
                    (268435454u32, 200usize),
                    (1073741816u32, 91usize),
                    (1073741816u32, 92usize),
                    (671088555u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (1073741816u32, 96usize),
                    (402653101u32, 97usize),
                    (268435454u32, 185usize),
                    (268435454u32, 193usize),
                    (268435454u32, 201usize),
                    (1073741816u32, 91usize),
                    (1073741816u32, 92usize),
                    (671088555u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (1073741816u32, 96usize),
                    (402653101u32, 97usize),
                    (268435454u32, 202usize),
                    (268435454u32, 210usize),
                    (268435454u32, 218usize),
                    (1073741816u32, 91usize),
                    (671088555u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 203usize),
                    (268435454u32, 211usize),
                    (268435454u32, 219usize),
                    (1073741816u32, 91usize),
                    (671088555u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 204usize),
                    (268435454u32, 212usize),
                    (268435454u32, 220usize),
                    (1073741816u32, 91usize),
                    (671088555u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 205usize),
                    (268435454u32, 213usize),
                    (268435454u32, 221usize),
                    (1073741816u32, 91usize),
                    (671088555u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 206usize),
                    (268435454u32, 214usize),
                    (268435454u32, 222usize),
                    (1073741816u32, 91usize),
                    (671088555u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 207usize),
                    (268435454u32, 215usize),
                    (268435454u32, 223usize),
                    (1073741816u32, 91usize),
                    (671088555u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 208usize),
                    (268435454u32, 216usize),
                    (268435454u32, 224usize),
                    (1073741816u32, 91usize),
                    (671088555u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 209usize),
                    (268435454u32, 217usize),
                    (268435454u32, 225usize),
                    (1073741816u32, 91usize),
                    (671088555u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (402653101u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 226usize),
                    (268435454u32, 234usize),
                    (268435454u32, 242usize),
                    (1073741816u32, 91usize),
                    (1073741816u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (1073741816u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 227usize),
                    (268435454u32, 235usize),
                    (268435454u32, 243usize),
                    (1073741816u32, 91usize),
                    (1073741816u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (1073741816u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 228usize),
                    (268435454u32, 236usize),
                    (268435454u32, 244usize),
                    (1073741816u32, 91usize),
                    (1073741816u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (1073741816u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 229usize),
                    (268435454u32, 237usize),
                    (268435454u32, 245usize),
                    (1073741816u32, 91usize),
                    (1073741816u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (1073741816u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 230usize),
                    (268435454u32, 238usize),
                    (268435454u32, 246usize),
                    (1073741816u32, 91usize),
                    (1073741816u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (1073741816u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 231usize),
                    (268435454u32, 239usize),
                    (268435454u32, 247usize),
                    (1073741816u32, 91usize),
                    (1073741816u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (1073741816u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 232usize),
                    (268435454u32, 240usize),
                    (268435454u32, 248usize),
                    (1073741816u32, 91usize),
                    (1073741816u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (1073741816u32, 96usize),
                    (1073741816u32, 97usize),
                    (268435454u32, 233usize),
                    (268435454u32, 241usize),
                    (268435454u32, 249usize),
                    (1073741816u32, 91usize),
                    (1073741816u32, 92usize),
                    (1073741816u32, 93usize),
                    (1073741816u32, 94usize),
                    (671088555u32, 95usize),
                    (1073741816u32, 96usize),
                    (1073741816u32, 97usize),
                ];
                let mut _vl = 0;
                while _vl < 41usize {
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
    ) -> Result<ConcreteGKRVerifierOutput, E::Error> {
        verify_gkr::<I, E>(external_challenges, initial_transcript, transcript_state)
    }
    #[inline(always)]
    fn verify_whir<I: NonDeterminismSource, E: ErrorCreator>(
        initial_transcript: &ConcreteInitialTranscript,
        transcript_state: &mut ::verifier_common::structs::TranscriptState,
        whir_batching_challenge: BabyBearExt4,
        base_layer_claims: &[BabyBearExt4],
        initial_claim_point: &[BabyBearExt4],
    ) -> Result<(), E::Error> {
        super::whir::verify_whir::<I, E>(
            initial_transcript,
            transcript_state,
            whir_batching_challenge,
            base_layer_claims,
            initial_claim_point,
        )
    }
}
