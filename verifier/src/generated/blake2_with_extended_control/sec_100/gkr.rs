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
    output_claims: &[BabyBearExt4; 330usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 409usize] = [
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
        (1usize, 136usize, 0usize),
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
        (2usize, 173usize, 174usize),
        (2usize, 175usize, 176usize),
        (2usize, 177usize, 178usize),
        (2usize, 179usize, 180usize),
        (2usize, 181usize, 182usize),
        (2usize, 183usize, 184usize),
        (2usize, 185usize, 186usize),
        (2usize, 187usize, 188usize),
        (2usize, 189usize, 190usize),
        (2usize, 191usize, 192usize),
        (2usize, 193usize, 194usize),
        (2usize, 195usize, 196usize),
        (2usize, 197usize, 198usize),
        (2usize, 199usize, 200usize),
        (2usize, 201usize, 202usize),
        (2usize, 203usize, 204usize),
        (2usize, 205usize, 206usize),
        (2usize, 207usize, 208usize),
        (2usize, 209usize, 210usize),
        (2usize, 211usize, 212usize),
        (2usize, 213usize, 214usize),
        (2usize, 215usize, 216usize),
        (2usize, 217usize, 218usize),
        (2usize, 219usize, 220usize),
        (2usize, 221usize, 222usize),
        (2usize, 223usize, 224usize),
        (2usize, 225usize, 226usize),
        (2usize, 227usize, 228usize),
        (2usize, 229usize, 230usize),
        (2usize, 231usize, 232usize),
        (2usize, 233usize, 234usize),
        (2usize, 235usize, 236usize),
        (2usize, 237usize, 238usize),
        (2usize, 239usize, 240usize),
        (2usize, 241usize, 242usize),
        (2usize, 243usize, 244usize),
        (2usize, 245usize, 246usize),
        (2usize, 247usize, 248usize),
        (2usize, 249usize, 250usize),
        (2usize, 251usize, 252usize),
        (2usize, 253usize, 254usize),
        (2usize, 255usize, 256usize),
        (2usize, 257usize, 258usize),
        (2usize, 259usize, 260usize),
        (2usize, 261usize, 262usize),
        (2usize, 263usize, 264usize),
        (2usize, 265usize, 266usize),
        (2usize, 267usize, 268usize),
        (2usize, 269usize, 270usize),
        (2usize, 271usize, 272usize),
        (2usize, 273usize, 274usize),
        (2usize, 275usize, 276usize),
        (2usize, 277usize, 278usize),
        (2usize, 279usize, 280usize),
        (2usize, 281usize, 282usize),
        (2usize, 283usize, 284usize),
        (2usize, 285usize, 286usize),
        (2usize, 287usize, 288usize),
        (2usize, 289usize, 290usize),
        (2usize, 291usize, 292usize),
        (2usize, 293usize, 294usize),
        (2usize, 295usize, 296usize),
        (2usize, 297usize, 298usize),
        (2usize, 299usize, 300usize),
        (2usize, 301usize, 302usize),
        (2usize, 303usize, 304usize),
        (2usize, 305usize, 306usize),
        (2usize, 307usize, 308usize),
        (2usize, 309usize, 310usize),
        (2usize, 311usize, 312usize),
        (2usize, 313usize, 314usize),
        (2usize, 315usize, 316usize),
        (2usize, 317usize, 318usize),
        (2usize, 319usize, 320usize),
        (2usize, 321usize, 322usize),
        (2usize, 323usize, 324usize),
        (2usize, 325usize, 326usize),
        (2usize, 327usize, 328usize),
        (1usize, 329usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
        (0usize, 0usize, 0usize),
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 188usize] = [
            (SimpleGateType::Copy, [337usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::Product,
                [342usize, 343usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [344usize, 345usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [346usize, 347usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [348usize, 349usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [350usize, 351usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [352usize, 353usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [354usize, 355usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [356usize, 357usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [358usize, 359usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [360usize, 361usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [362usize, 363usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [364usize, 365usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [366usize, 367usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [368usize, 369usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [370usize, 371usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [372usize, 373usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [374usize, 375usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [376usize, 377usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [378usize, 379usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [380usize, 381usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [382usize, 383usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [384usize, 385usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [386usize, 387usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [388usize, 389usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [390usize, 391usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [392usize, 393usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [394usize, 395usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [396usize, 397usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [398usize, 399usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [400usize, 401usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [402usize, 403usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [404usize, 405usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [406usize, 407usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [408usize, 409usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [410usize, 411usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [412usize, 413usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [414usize, 415usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [416usize, 417usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [418usize, 419usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [420usize, 421usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [422usize, 423usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [424usize, 425usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [426usize, 427usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [428usize, 429usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupWithSetup,
                [430usize, 234usize, 340usize, 0usize],
            ),
            (SimpleGateType::Copy, [431usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupWithSetup,
                [338usize, 235usize, 341usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [339usize, 432usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [433usize, 434usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [435usize, 436usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [437usize, 438usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [439usize, 440usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [441usize, 442usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [443usize, 444usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [445usize, 446usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [447usize, 448usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [449usize, 450usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [451usize, 452usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [453usize, 454usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [455usize, 456usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [457usize, 458usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [459usize, 460usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [461usize, 462usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [463usize, 464usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [465usize, 466usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [467usize, 468usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [469usize, 470usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [471usize, 472usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [473usize, 474usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [475usize, 476usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [477usize, 478usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [479usize, 480usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [481usize, 482usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [483usize, 484usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [485usize, 486usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [487usize, 488usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [489usize, 490usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [491usize, 492usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [493usize, 494usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [495usize, 496usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [497usize, 498usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [499usize, 500usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [501usize, 502usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [503usize, 504usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [505usize, 506usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [507usize, 508usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [509usize, 510usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [511usize, 512usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [513usize, 514usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [515usize, 516usize, 0usize, 0usize],
            ),
            (SimpleGateType::Copy, [517usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupWithSetup,
                [518usize, 236usize, 519usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [520usize, 521usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [522usize, 523usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [524usize, 525usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [526usize, 527usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [528usize, 529usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [530usize, 531usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [532usize, 533usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [534usize, 535usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [536usize, 537usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [538usize, 539usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [540usize, 541usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [542usize, 543usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [544usize, 545usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [546usize, 547usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [548usize, 549usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [550usize, 551usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [552usize, 553usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [554usize, 555usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [556usize, 557usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [558usize, 559usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [560usize, 561usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [562usize, 563usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [564usize, 565usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [566usize, 567usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [568usize, 569usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [570usize, 571usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [572usize, 573usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [574usize, 575usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [576usize, 577usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [578usize, 579usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [580usize, 581usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [582usize, 583usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [584usize, 585usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [586usize, 587usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [588usize, 589usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [590usize, 591usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [592usize, 593usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [594usize, 595usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [596usize, 597usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [598usize, 599usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [600usize, 601usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [602usize, 603usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [604usize, 605usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [606usize, 607usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [608usize, 609usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [610usize, 611usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [612usize, 613usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [614usize, 615usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [616usize, 617usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [618usize, 619usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [620usize, 621usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [622usize, 623usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [624usize, 625usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [626usize, 627usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [628usize, 629usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [630usize, 631usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [632usize, 633usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [634usize, 635usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [636usize, 637usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [638usize, 639usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [640usize, 641usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [642usize, 643usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [644usize, 645usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [646usize, 647usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [648usize, 649usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [650usize, 651usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [652usize, 653usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [654usize, 655usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [656usize, 657usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [658usize, 659usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [660usize, 661usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [662usize, 663usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [664usize, 665usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [666usize, 667usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [668usize, 669usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [670usize, 671usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [672usize, 673usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [674usize, 675usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [676usize, 677usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [678usize, 679usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [680usize, 681usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [682usize, 683usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [684usize, 685usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [686usize, 687usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [688usize, 689usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [690usize, 691usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [692usize, 693usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [694usize, 695usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [696usize, 697usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [698usize, 699usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [700usize, 701usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [702usize, 703usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [704usize, 705usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [706usize, 707usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [708usize, 709usize, 0usize, 0usize],
            ),
        ];
        let mut _sg = 0;
        while _sg < 188usize {
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
            const VAL_COLS: [(usize, usize); 6usize] = [
                (1073741816usize, 0usize),
                (0usize, 0usize),
                (0usize, 0usize),
                (0usize, 1usize),
                (0usize, 2usize),
                (0usize, 2usize),
            ];
            const VAL_VL_TERMS: [(usize, usize); 5usize] = [
                (190usize, 268435454usize),
                (187usize, 536870908usize),
                (188usize, 268435454usize),
                (301usize, 16777216usize),
                (135usize, 1996488705usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(337usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(337usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(337usize, 1744830467usize)];
            let val =
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
                (334usize, 1744830467usize),
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
            const VAL_QI: [(usize, usize); 1usize] = [(9usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(12usize, 268435454usize), (13usize, 1744830467usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(3usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(3usize, 268435454usize), (14usize, 1744830467usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(237usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 268309694usize),
                (15usize, 1744830467usize),
                (237usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(15usize, 268435454usize), (269usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(16usize, 1744830467usize), (269usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(238usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 671030187usize),
                (17usize, 1744830467usize),
                (238usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(17usize, 268435454usize), (270usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(18usize, 1744830467usize), (270usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(241usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1878952882usize),
                (19usize, 1744830467usize),
                (241usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(19usize, 268435454usize), (271usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(20usize, 1744830467usize), (271usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(242usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1342074934usize),
                (21usize, 1744830467usize),
                (242usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(21usize, 268435454usize), (272usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(22usize, 1744830467usize), (272usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(245usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1207826599usize),
                (23usize, 1744830467usize),
                (245usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(23usize, 268435454usize), (273usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(24usize, 1744830467usize), (273usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(246usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1342144278usize),
                (25usize, 1744830467usize),
                (246usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(25usize, 268435454usize), (274usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(26usize, 1744830467usize), (274usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(249usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 805172442usize),
                (27usize, 1744830467usize),
                (249usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(27usize, 268435454usize), (275usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(28usize, 1744830467usize), (275usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(250usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1073651544usize),
                (29usize, 1744830467usize),
                (250usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(29usize, 268435454usize), (276usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(30usize, 1744830467usize), (276usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(253usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1744785411usize),
                (31usize, 1744830467usize),
                (253usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(31usize, 268435454usize), (277usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(32usize, 1744830467usize), (277usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(254usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1342133014usize),
                (33usize, 1744830467usize),
                (254usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(33usize, 268435454usize), (278usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(34usize, 1744830467usize), (278usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(257usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1073684728usize),
                (35usize, 1744830467usize),
                (257usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(35usize, 268435454usize), (279usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(36usize, 1744830467usize), (279usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(258usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 671003979usize),
                (37usize, 1744830467usize),
                (258usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(37usize, 268435454usize), (280usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(38usize, 1744830467usize), (280usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(261usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1476276133usize),
                (39usize, 1744830467usize),
                (261usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(39usize, 268435454usize), (281usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(40usize, 1744830467usize), (281usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(262usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1207942343usize),
                (41usize, 1744830467usize),
                (262usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(41usize, 268435454usize), (282usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(42usize, 1744830467usize), (282usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(265usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1342065270usize),
                (43usize, 1744830467usize),
                (265usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(43usize, 268435454usize), (283usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(44usize, 1744830467usize), (283usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(266usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 2013215745usize),
                (45usize, 1744830467usize),
                (266usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(45usize, 268435454usize), (284usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(46usize, 1744830467usize), (284usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(285usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 805180538usize),
                (47usize, 1744830467usize),
                (285usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(286usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 671030731usize),
                (48usize, 1744830467usize),
                (286usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(287usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1878952882usize),
                (49usize, 1744830467usize),
                (287usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(288usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1342074934usize),
                (50usize, 1744830467usize),
                (288usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(289usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1207826599usize),
                (51usize, 1744830467usize),
                (289usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(290usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1342144278usize),
                (52usize, 1744830467usize),
                (290usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(291usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 805172442usize),
                (53usize, 1744830467usize),
                (291usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(292usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1073651544usize),
                (54usize, 1744830467usize),
                (292usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(295usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1073684728usize),
                (55usize, 1744830467usize),
                (295usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(296usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 671003979usize),
                (56usize, 1744830467usize),
                (296usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(299usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1342065270usize),
                (57usize, 1744830467usize),
                (299usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(300usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 2013215745usize),
                (58usize, 1744830467usize),
                (300usize, 268435454usize),
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
                [(2usize, 1usize), (3usize, 1usize), (14usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (3usize, 671043723usize),
                (293usize, 1744830467usize),
                (293usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(59usize, 1744830467usize), (293usize, 268435454usize)];
            let val =
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
                [(2usize, 1usize), (3usize, 1usize), (14usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (3usize, 1342133014usize),
                (294usize, 1744830467usize),
                (294usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(60usize, 1744830467usize), (294usize, 268435454usize)];
            let val =
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
                [(2usize, 1usize), (3usize, 1usize), (14usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (3usize, 536849980usize),
                (297usize, 1744830467usize),
                (297usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(61usize, 1744830467usize), (297usize, 268435454usize)];
            let val =
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
                [(2usize, 1usize), (3usize, 1usize), (14usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (3usize, 805183770usize),
                (298usize, 1744830467usize),
                (298usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(62usize, 1744830467usize), (298usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(2usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(63usize, 1744830467usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(2usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(2usize, 268435454usize), (64usize, 1744830467usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(64usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(65usize, 1744830467usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(64usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(66usize, 1744830467usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(64usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(67usize, 1744830467usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(64usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(68usize, 1744830467usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(64usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(69usize, 1744830467usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(64usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(70usize, 1744830467usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(64usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(71usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(10usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(64usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(72usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(11usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(64usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(73usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(12usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(64usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(74usize, 1744830467usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(63usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(75usize, 1744830467usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(63usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(76usize, 1744830467usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(63usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(77usize, 1744830467usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(63usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(78usize, 1744830467usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(63usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(79usize, 1744830467usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(63usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(9usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(63usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(81usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(10usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(63usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(82usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(11usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(63usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(83usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(12usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(63usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(84usize, 1744830467usize)];
            let val =
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (76usize, 2usize),
                (77usize, 2usize),
                (79usize, 2usize),
                (81usize, 2usize),
                (82usize, 2usize),
                (84usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 42usize] = [
                (302usize, 268435454usize),
                (330usize, 268435454usize),
                (324usize, 268435454usize),
                (316usize, 268435454usize),
                (320usize, 268435454usize),
                (306usize, 268435454usize),
                (326usize, 268435454usize),
                (328usize, 268435454usize),
                (314usize, 268435454usize),
                (322usize, 268435454usize),
                (237usize, 268435454usize),
                (302usize, 1744830467usize),
                (314usize, 268435454usize),
                (330usize, 1744830467usize),
                (308usize, 268435454usize),
                (324usize, 1744830467usize),
                (265usize, 268435454usize),
                (316usize, 1744830467usize),
                (304usize, 268435454usize),
                (320usize, 1744830467usize),
                (245usize, 268435454usize),
                (306usize, 1744830467usize),
                (310usize, 268435454usize),
                (326usize, 1744830467usize),
                (312usize, 268435454usize),
                (328usize, 1744830467usize),
                (261usize, 268435454usize),
                (314usize, 1744830467usize),
                (306usize, 268435454usize),
                (322usize, 1744830467usize),
                (261usize, 268435454usize),
                (330usize, 1744830467usize),
                (249usize, 268435454usize),
                (324usize, 1744830467usize),
                (241usize, 268435454usize),
                (320usize, 1744830467usize),
                (253usize, 268435454usize),
                (326usize, 1744830467usize),
                (257usize, 268435454usize),
                (328usize, 1744830467usize),
                (245usize, 268435454usize),
                (322usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(85usize, 1744830467usize)];
            let val =
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (76usize, 2usize),
                (77usize, 2usize),
                (79usize, 2usize),
                (81usize, 2usize),
                (82usize, 2usize),
                (84usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 42usize] = [
                (303usize, 268435454usize),
                (331usize, 268435454usize),
                (325usize, 268435454usize),
                (317usize, 268435454usize),
                (321usize, 268435454usize),
                (307usize, 268435454usize),
                (327usize, 268435454usize),
                (329usize, 268435454usize),
                (315usize, 268435454usize),
                (323usize, 268435454usize),
                (238usize, 268435454usize),
                (303usize, 1744830467usize),
                (315usize, 268435454usize),
                (331usize, 1744830467usize),
                (309usize, 268435454usize),
                (325usize, 1744830467usize),
                (266usize, 268435454usize),
                (317usize, 1744830467usize),
                (305usize, 268435454usize),
                (321usize, 1744830467usize),
                (246usize, 268435454usize),
                (307usize, 1744830467usize),
                (311usize, 268435454usize),
                (327usize, 1744830467usize),
                (313usize, 268435454usize),
                (329usize, 1744830467usize),
                (262usize, 268435454usize),
                (315usize, 1744830467usize),
                (307usize, 268435454usize),
                (323usize, 1744830467usize),
                (262usize, 268435454usize),
                (331usize, 1744830467usize),
                (250usize, 268435454usize),
                (325usize, 1744830467usize),
                (242usize, 268435454usize),
                (321usize, 1744830467usize),
                (254usize, 268435454usize),
                (327usize, 1744830467usize),
                (258usize, 268435454usize),
                (329usize, 1744830467usize),
                (246usize, 268435454usize),
                (323usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(86usize, 1744830467usize)];
            let val =
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (76usize, 2usize),
                (77usize, 2usize),
                (78usize, 2usize),
                (80usize, 2usize),
                (82usize, 2usize),
                (83usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 42usize] = [
                (304usize, 268435454usize),
                (322usize, 268435454usize),
                (318usize, 268435454usize),
                (320usize, 268435454usize),
                (302usize, 268435454usize),
                (326usize, 268435454usize),
                (312usize, 268435454usize),
                (324usize, 268435454usize),
                (332usize, 268435454usize),
                (306usize, 268435454usize),
                (241usize, 268435454usize),
                (304usize, 1744830467usize),
                (306usize, 268435454usize),
                (322usize, 1744830467usize),
                (302usize, 268435454usize),
                (318usize, 1744830467usize),
                (304usize, 268435454usize),
                (320usize, 1744830467usize),
                (237usize, 268435454usize),
                (302usize, 1744830467usize),
                (310usize, 268435454usize),
                (326usize, 1744830467usize),
                (257usize, 268435454usize),
                (312usize, 1744830467usize),
                (308usize, 268435454usize),
                (324usize, 1744830467usize),
                (316usize, 268435454usize),
                (332usize, 1744830467usize),
                (245usize, 268435454usize),
                (306usize, 1744830467usize),
                (245usize, 268435454usize),
                (322usize, 1744830467usize),
                (237usize, 268435454usize),
                (318usize, 1744830467usize),
                (241usize, 268435454usize),
                (320usize, 1744830467usize),
                (253usize, 268435454usize),
                (326usize, 1744830467usize),
                (249usize, 268435454usize),
                (324usize, 1744830467usize),
                (265usize, 268435454usize),
                (332usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(87usize, 1744830467usize)];
            let val =
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (76usize, 2usize),
                (77usize, 2usize),
                (78usize, 2usize),
                (80usize, 2usize),
                (82usize, 2usize),
                (83usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 42usize] = [
                (305usize, 268435454usize),
                (323usize, 268435454usize),
                (319usize, 268435454usize),
                (321usize, 268435454usize),
                (303usize, 268435454usize),
                (327usize, 268435454usize),
                (313usize, 268435454usize),
                (325usize, 268435454usize),
                (333usize, 268435454usize),
                (307usize, 268435454usize),
                (242usize, 268435454usize),
                (305usize, 1744830467usize),
                (307usize, 268435454usize),
                (323usize, 1744830467usize),
                (303usize, 268435454usize),
                (319usize, 1744830467usize),
                (305usize, 268435454usize),
                (321usize, 1744830467usize),
                (238usize, 268435454usize),
                (303usize, 1744830467usize),
                (311usize, 268435454usize),
                (327usize, 1744830467usize),
                (258usize, 268435454usize),
                (313usize, 1744830467usize),
                (309usize, 268435454usize),
                (325usize, 1744830467usize),
                (317usize, 268435454usize),
                (333usize, 1744830467usize),
                (246usize, 268435454usize),
                (307usize, 1744830467usize),
                (246usize, 268435454usize),
                (323usize, 1744830467usize),
                (238usize, 268435454usize),
                (319usize, 1744830467usize),
                (242usize, 268435454usize),
                (321usize, 1744830467usize),
                (254usize, 268435454usize),
                (327usize, 1744830467usize),
                (250usize, 268435454usize),
                (325usize, 1744830467usize),
                (266usize, 268435454usize),
                (333usize, 1744830467usize),
            ];
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
            const VAL_QO: [(usize, usize); 23usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (77usize, 2usize),
                (83usize, 2usize),
                (84usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 36usize] = [
                (306usize, 268435454usize),
                (310usize, 268435454usize),
                (326usize, 268435454usize),
                (308usize, 268435454usize),
                (312usize, 268435454usize),
                (314usize, 268435454usize),
                (304usize, 268435454usize),
                (316usize, 268435454usize),
                (330usize, 268435454usize),
                (318usize, 268435454usize),
                (245usize, 268435454usize),
                (306usize, 1744830467usize),
                (253usize, 268435454usize),
                (310usize, 1744830467usize),
                (310usize, 268435454usize),
                (326usize, 1744830467usize),
                (249usize, 268435454usize),
                (308usize, 1744830467usize),
                (257usize, 268435454usize),
                (312usize, 1744830467usize),
                (261usize, 268435454usize),
                (314usize, 1744830467usize),
                (241usize, 268435454usize),
                (304usize, 1744830467usize),
                (265usize, 268435454usize),
                (316usize, 1744830467usize),
                (314usize, 268435454usize),
                (330usize, 1744830467usize),
                (302usize, 268435454usize),
                (318usize, 1744830467usize),
                (253usize, 268435454usize),
                (326usize, 1744830467usize),
                (261usize, 268435454usize),
                (330usize, 1744830467usize),
                (237usize, 268435454usize),
                (318usize, 1744830467usize),
            ];
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
            const VAL_QO: [(usize, usize); 23usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (77usize, 2usize),
                (83usize, 2usize),
                (84usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 36usize] = [
                (307usize, 268435454usize),
                (311usize, 268435454usize),
                (327usize, 268435454usize),
                (309usize, 268435454usize),
                (313usize, 268435454usize),
                (315usize, 268435454usize),
                (305usize, 268435454usize),
                (317usize, 268435454usize),
                (331usize, 268435454usize),
                (319usize, 268435454usize),
                (246usize, 268435454usize),
                (307usize, 1744830467usize),
                (254usize, 268435454usize),
                (311usize, 1744830467usize),
                (311usize, 268435454usize),
                (327usize, 1744830467usize),
                (250usize, 268435454usize),
                (309usize, 1744830467usize),
                (258usize, 268435454usize),
                (313usize, 1744830467usize),
                (262usize, 268435454usize),
                (315usize, 1744830467usize),
                (242usize, 268435454usize),
                (305usize, 1744830467usize),
                (266usize, 268435454usize),
                (317usize, 1744830467usize),
                (315usize, 268435454usize),
                (331usize, 1744830467usize),
                (303usize, 268435454usize),
                (319usize, 1744830467usize),
                (254usize, 268435454usize),
                (327usize, 1744830467usize),
                (262usize, 268435454usize),
                (331usize, 1744830467usize),
                (238usize, 268435454usize),
                (319usize, 1744830467usize),
            ];
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
            const VAL_QO: [(usize, usize); 25usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (76usize, 2usize),
                (80usize, 2usize),
                (81usize, 2usize),
                (82usize, 2usize),
                (83usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 40usize] = [
                (308usize, 268435454usize),
                (318usize, 268435454usize),
                (302usize, 268435454usize),
                (304usize, 268435454usize),
                (316usize, 268435454usize),
                (322usize, 268435454usize),
                (332usize, 268435454usize),
                (330usize, 268435454usize),
                (320usize, 268435454usize),
                (310usize, 268435454usize),
                (249usize, 268435454usize),
                (308usize, 1744830467usize),
                (302usize, 268435454usize),
                (318usize, 1744830467usize),
                (237usize, 268435454usize),
                (302usize, 1744830467usize),
                (241usize, 268435454usize),
                (304usize, 1744830467usize),
                (265usize, 268435454usize),
                (316usize, 1744830467usize),
                (306usize, 268435454usize),
                (322usize, 1744830467usize),
                (316usize, 268435454usize),
                (332usize, 1744830467usize),
                (314usize, 268435454usize),
                (330usize, 1744830467usize),
                (304usize, 268435454usize),
                (320usize, 1744830467usize),
                (253usize, 268435454usize),
                (310usize, 1744830467usize),
                (237usize, 268435454usize),
                (318usize, 1744830467usize),
                (245usize, 268435454usize),
                (322usize, 1744830467usize),
                (265usize, 268435454usize),
                (332usize, 1744830467usize),
                (261usize, 268435454usize),
                (330usize, 1744830467usize),
                (241usize, 268435454usize),
                (320usize, 1744830467usize),
            ];
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
            const VAL_QO: [(usize, usize); 25usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (76usize, 2usize),
                (80usize, 2usize),
                (81usize, 2usize),
                (82usize, 2usize),
                (83usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 40usize] = [
                (309usize, 268435454usize),
                (319usize, 268435454usize),
                (303usize, 268435454usize),
                (305usize, 268435454usize),
                (317usize, 268435454usize),
                (323usize, 268435454usize),
                (333usize, 268435454usize),
                (331usize, 268435454usize),
                (321usize, 268435454usize),
                (311usize, 268435454usize),
                (250usize, 268435454usize),
                (309usize, 1744830467usize),
                (303usize, 268435454usize),
                (319usize, 1744830467usize),
                (238usize, 268435454usize),
                (303usize, 1744830467usize),
                (242usize, 268435454usize),
                (305usize, 1744830467usize),
                (266usize, 268435454usize),
                (317usize, 1744830467usize),
                (307usize, 268435454usize),
                (323usize, 1744830467usize),
                (317usize, 268435454usize),
                (333usize, 1744830467usize),
                (315usize, 268435454usize),
                (331usize, 1744830467usize),
                (305usize, 268435454usize),
                (321usize, 1744830467usize),
                (254usize, 268435454usize),
                (311usize, 1744830467usize),
                (238usize, 268435454usize),
                (319usize, 1744830467usize),
                (246usize, 268435454usize),
                (323usize, 1744830467usize),
                (266usize, 268435454usize),
                (333usize, 1744830467usize),
                (262usize, 268435454usize),
                (331usize, 1744830467usize),
                (242usize, 268435454usize),
                (321usize, 1744830467usize),
            ];
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
            const VAL_QO: [(usize, usize); 25usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (76usize, 2usize),
                (78usize, 2usize),
                (81usize, 2usize),
                (82usize, 2usize),
                (83usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 40usize] = [
                (310usize, 268435454usize),
                (320usize, 268435454usize),
                (312usize, 268435454usize),
                (328usize, 268435454usize),
                (306usize, 268435454usize),
                (302usize, 268435454usize),
                (330usize, 268435454usize),
                (326usize, 268435454usize),
                (324usize, 268435454usize),
                (316usize, 268435454usize),
                (253usize, 268435454usize),
                (310usize, 1744830467usize),
                (304usize, 268435454usize),
                (320usize, 1744830467usize),
                (257usize, 268435454usize),
                (312usize, 1744830467usize),
                (312usize, 268435454usize),
                (328usize, 1744830467usize),
                (245usize, 268435454usize),
                (306usize, 1744830467usize),
                (237usize, 268435454usize),
                (302usize, 1744830467usize),
                (314usize, 268435454usize),
                (330usize, 1744830467usize),
                (310usize, 268435454usize),
                (326usize, 1744830467usize),
                (308usize, 268435454usize),
                (324usize, 1744830467usize),
                (265usize, 268435454usize),
                (316usize, 1744830467usize),
                (241usize, 268435454usize),
                (320usize, 1744830467usize),
                (257usize, 268435454usize),
                (328usize, 1744830467usize),
                (261usize, 268435454usize),
                (330usize, 1744830467usize),
                (253usize, 268435454usize),
                (326usize, 1744830467usize),
                (249usize, 268435454usize),
                (324usize, 1744830467usize),
            ];
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
            const VAL_QO: [(usize, usize); 25usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (76usize, 2usize),
                (78usize, 2usize),
                (81usize, 2usize),
                (82usize, 2usize),
                (83usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 40usize] = [
                (311usize, 268435454usize),
                (321usize, 268435454usize),
                (313usize, 268435454usize),
                (329usize, 268435454usize),
                (307usize, 268435454usize),
                (303usize, 268435454usize),
                (331usize, 268435454usize),
                (327usize, 268435454usize),
                (325usize, 268435454usize),
                (317usize, 268435454usize),
                (254usize, 268435454usize),
                (311usize, 1744830467usize),
                (305usize, 268435454usize),
                (321usize, 1744830467usize),
                (258usize, 268435454usize),
                (313usize, 1744830467usize),
                (313usize, 268435454usize),
                (329usize, 1744830467usize),
                (246usize, 268435454usize),
                (307usize, 1744830467usize),
                (238usize, 268435454usize),
                (303usize, 1744830467usize),
                (315usize, 268435454usize),
                (331usize, 1744830467usize),
                (311usize, 268435454usize),
                (327usize, 1744830467usize),
                (309usize, 268435454usize),
                (325usize, 1744830467usize),
                (266usize, 268435454usize),
                (317usize, 1744830467usize),
                (242usize, 268435454usize),
                (321usize, 1744830467usize),
                (258usize, 268435454usize),
                (329usize, 1744830467usize),
                (262usize, 268435454usize),
                (331usize, 1744830467usize),
                (254usize, 268435454usize),
                (327usize, 1744830467usize),
                (250usize, 268435454usize),
                (325usize, 1744830467usize),
            ];
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
            const VAL_QO: [(usize, usize); 24usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (76usize, 2usize),
                (78usize, 2usize),
                (80usize, 2usize),
                (81usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 38usize] = [
                (312usize, 268435454usize),
                (332usize, 268435454usize),
                (306usize, 268435454usize),
                (326usize, 268435454usize),
                (310usize, 268435454usize),
                (324usize, 268435454usize),
                (328usize, 268435454usize),
                (304usize, 268435454usize),
                (308usize, 268435454usize),
                (314usize, 268435454usize),
                (257usize, 268435454usize),
                (312usize, 1744830467usize),
                (316usize, 268435454usize),
                (332usize, 1744830467usize),
                (245usize, 268435454usize),
                (306usize, 1744830467usize),
                (310usize, 268435454usize),
                (326usize, 1744830467usize),
                (253usize, 268435454usize),
                (310usize, 1744830467usize),
                (308usize, 268435454usize),
                (324usize, 1744830467usize),
                (312usize, 268435454usize),
                (328usize, 1744830467usize),
                (241usize, 268435454usize),
                (304usize, 1744830467usize),
                (249usize, 268435454usize),
                (308usize, 1744830467usize),
                (261usize, 268435454usize),
                (314usize, 1744830467usize),
                (265usize, 268435454usize),
                (332usize, 1744830467usize),
                (253usize, 268435454usize),
                (326usize, 1744830467usize),
                (249usize, 268435454usize),
                (324usize, 1744830467usize),
                (257usize, 268435454usize),
                (328usize, 1744830467usize),
            ];
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
            const VAL_QO: [(usize, usize); 24usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (76usize, 2usize),
                (78usize, 2usize),
                (80usize, 2usize),
                (81usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 38usize] = [
                (313usize, 268435454usize),
                (333usize, 268435454usize),
                (307usize, 268435454usize),
                (327usize, 268435454usize),
                (311usize, 268435454usize),
                (325usize, 268435454usize),
                (329usize, 268435454usize),
                (305usize, 268435454usize),
                (309usize, 268435454usize),
                (315usize, 268435454usize),
                (258usize, 268435454usize),
                (313usize, 1744830467usize),
                (317usize, 268435454usize),
                (333usize, 1744830467usize),
                (246usize, 268435454usize),
                (307usize, 1744830467usize),
                (311usize, 268435454usize),
                (327usize, 1744830467usize),
                (254usize, 268435454usize),
                (311usize, 1744830467usize),
                (309usize, 268435454usize),
                (325usize, 1744830467usize),
                (313usize, 268435454usize),
                (329usize, 1744830467usize),
                (242usize, 268435454usize),
                (305usize, 1744830467usize),
                (250usize, 268435454usize),
                (309usize, 1744830467usize),
                (262usize, 268435454usize),
                (315usize, 1744830467usize),
                (266usize, 268435454usize),
                (333usize, 1744830467usize),
                (254usize, 268435454usize),
                (327usize, 1744830467usize),
                (250usize, 268435454usize),
                (325usize, 1744830467usize),
                (258usize, 268435454usize),
                (329usize, 1744830467usize),
            ];
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
            const VAL_QO: [(usize, usize); 25usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (76usize, 2usize),
                (77usize, 2usize),
                (78usize, 2usize),
                (79usize, 2usize),
                (80usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 40usize] = [
                (314usize, 268435454usize),
                (328usize, 268435454usize),
                (332usize, 268435454usize),
                (324usize, 268435454usize),
                (322usize, 268435454usize),
                (318usize, 268435454usize),
                (310usize, 268435454usize),
                (308usize, 268435454usize),
                (302usize, 268435454usize),
                (304usize, 268435454usize),
                (261usize, 268435454usize),
                (314usize, 1744830467usize),
                (312usize, 268435454usize),
                (328usize, 1744830467usize),
                (316usize, 268435454usize),
                (332usize, 1744830467usize),
                (308usize, 268435454usize),
                (324usize, 1744830467usize),
                (306usize, 268435454usize),
                (322usize, 1744830467usize),
                (302usize, 268435454usize),
                (318usize, 1744830467usize),
                (253usize, 268435454usize),
                (310usize, 1744830467usize),
                (249usize, 268435454usize),
                (308usize, 1744830467usize),
                (237usize, 268435454usize),
                (302usize, 1744830467usize),
                (241usize, 268435454usize),
                (304usize, 1744830467usize),
                (257usize, 268435454usize),
                (328usize, 1744830467usize),
                (265usize, 268435454usize),
                (332usize, 1744830467usize),
                (249usize, 268435454usize),
                (324usize, 1744830467usize),
                (245usize, 268435454usize),
                (322usize, 1744830467usize),
                (237usize, 268435454usize),
                (318usize, 1744830467usize),
            ];
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
            const VAL_QO: [(usize, usize); 25usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (76usize, 2usize),
                (77usize, 2usize),
                (78usize, 2usize),
                (79usize, 2usize),
                (80usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 40usize] = [
                (315usize, 268435454usize),
                (329usize, 268435454usize),
                (333usize, 268435454usize),
                (325usize, 268435454usize),
                (323usize, 268435454usize),
                (319usize, 268435454usize),
                (311usize, 268435454usize),
                (309usize, 268435454usize),
                (303usize, 268435454usize),
                (305usize, 268435454usize),
                (262usize, 268435454usize),
                (315usize, 1744830467usize),
                (313usize, 268435454usize),
                (329usize, 1744830467usize),
                (317usize, 268435454usize),
                (333usize, 1744830467usize),
                (309usize, 268435454usize),
                (325usize, 1744830467usize),
                (307usize, 268435454usize),
                (323usize, 1744830467usize),
                (303usize, 268435454usize),
                (319usize, 1744830467usize),
                (254usize, 268435454usize),
                (311usize, 1744830467usize),
                (250usize, 268435454usize),
                (309usize, 1744830467usize),
                (238usize, 268435454usize),
                (303usize, 1744830467usize),
                (242usize, 268435454usize),
                (305usize, 1744830467usize),
                (258usize, 268435454usize),
                (329usize, 1744830467usize),
                (266usize, 268435454usize),
                (333usize, 1744830467usize),
                (250usize, 268435454usize),
                (325usize, 1744830467usize),
                (246usize, 268435454usize),
                (323usize, 1744830467usize),
                (238usize, 268435454usize),
                (319usize, 1744830467usize),
            ];
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
            const VAL_QO: [(usize, usize); 26usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (77usize, 2usize),
                (78usize, 2usize),
                (79usize, 2usize),
                (81usize, 2usize),
                (82usize, 2usize),
                (83usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 42usize] = [
                (316usize, 268435454usize),
                (314usize, 268435454usize),
                (328usize, 268435454usize),
                (330usize, 268435454usize),
                (332usize, 268435454usize),
                (308usize, 268435454usize),
                (322usize, 268435454usize),
                (320usize, 268435454usize),
                (318usize, 268435454usize),
                (312usize, 268435454usize),
                (265usize, 268435454usize),
                (316usize, 1744830467usize),
                (261usize, 268435454usize),
                (314usize, 1744830467usize),
                (312usize, 268435454usize),
                (328usize, 1744830467usize),
                (314usize, 268435454usize),
                (330usize, 1744830467usize),
                (316usize, 268435454usize),
                (332usize, 1744830467usize),
                (249usize, 268435454usize),
                (308usize, 1744830467usize),
                (306usize, 268435454usize),
                (322usize, 1744830467usize),
                (304usize, 268435454usize),
                (320usize, 1744830467usize),
                (302usize, 268435454usize),
                (318usize, 1744830467usize),
                (257usize, 268435454usize),
                (312usize, 1744830467usize),
                (257usize, 268435454usize),
                (328usize, 1744830467usize),
                (261usize, 268435454usize),
                (330usize, 1744830467usize),
                (265usize, 268435454usize),
                (332usize, 1744830467usize),
                (245usize, 268435454usize),
                (322usize, 1744830467usize),
                (241usize, 268435454usize),
                (320usize, 1744830467usize),
                (237usize, 268435454usize),
                (318usize, 1744830467usize),
            ];
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
            const VAL_QO: [(usize, usize); 26usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (77usize, 2usize),
                (78usize, 2usize),
                (79usize, 2usize),
                (81usize, 2usize),
                (82usize, 2usize),
                (83usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 42usize] = [
                (317usize, 268435454usize),
                (315usize, 268435454usize),
                (329usize, 268435454usize),
                (331usize, 268435454usize),
                (333usize, 268435454usize),
                (309usize, 268435454usize),
                (323usize, 268435454usize),
                (321usize, 268435454usize),
                (319usize, 268435454usize),
                (313usize, 268435454usize),
                (266usize, 268435454usize),
                (317usize, 1744830467usize),
                (262usize, 268435454usize),
                (315usize, 1744830467usize),
                (313usize, 268435454usize),
                (329usize, 1744830467usize),
                (315usize, 268435454usize),
                (331usize, 1744830467usize),
                (317usize, 268435454usize),
                (333usize, 1744830467usize),
                (250usize, 268435454usize),
                (309usize, 1744830467usize),
                (307usize, 268435454usize),
                (323usize, 1744830467usize),
                (305usize, 268435454usize),
                (321usize, 1744830467usize),
                (303usize, 268435454usize),
                (319usize, 1744830467usize),
                (258usize, 268435454usize),
                (313usize, 1744830467usize),
                (258usize, 268435454usize),
                (329usize, 1744830467usize),
                (262usize, 268435454usize),
                (331usize, 1744830467usize),
                (266usize, 268435454usize),
                (333usize, 1744830467usize),
                (246usize, 268435454usize),
                (323usize, 1744830467usize),
                (242usize, 268435454usize),
                (321usize, 1744830467usize),
                (238usize, 268435454usize),
                (319usize, 1744830467usize),
            ];
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
            const VAL_QO: [(usize, usize); 25usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (75usize, 2usize),
                (77usize, 2usize),
                (79usize, 2usize),
                (83usize, 2usize),
                (84usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 40usize] = [
                (318usize, 268435454usize),
                (304usize, 268435454usize),
                (322usize, 268435454usize),
                (306usize, 268435454usize),
                (330usize, 268435454usize),
                (310usize, 268435454usize),
                (302usize, 268435454usize),
                (312usize, 268435454usize),
                (326usize, 268435454usize),
                (332usize, 268435454usize),
                (302usize, 268435454usize),
                (318usize, 1744830467usize),
                (241usize, 268435454usize),
                (304usize, 1744830467usize),
                (306usize, 268435454usize),
                (322usize, 1744830467usize),
                (245usize, 268435454usize),
                (306usize, 1744830467usize),
                (314usize, 268435454usize),
                (330usize, 1744830467usize),
                (253usize, 268435454usize),
                (310usize, 1744830467usize),
                (237usize, 268435454usize),
                (302usize, 1744830467usize),
                (257usize, 268435454usize),
                (312usize, 1744830467usize),
                (310usize, 268435454usize),
                (326usize, 1744830467usize),
                (316usize, 268435454usize),
                (332usize, 1744830467usize),
                (237usize, 268435454usize),
                (318usize, 1744830467usize),
                (245usize, 268435454usize),
                (322usize, 1744830467usize),
                (261usize, 268435454usize),
                (330usize, 1744830467usize),
                (253usize, 268435454usize),
                (326usize, 1744830467usize),
                (265usize, 268435454usize),
                (332usize, 1744830467usize),
            ];
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
            const VAL_QO: [(usize, usize); 25usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (75usize, 2usize),
                (77usize, 2usize),
                (79usize, 2usize),
                (83usize, 2usize),
                (84usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 40usize] = [
                (319usize, 268435454usize),
                (305usize, 268435454usize),
                (323usize, 268435454usize),
                (307usize, 268435454usize),
                (331usize, 268435454usize),
                (311usize, 268435454usize),
                (303usize, 268435454usize),
                (313usize, 268435454usize),
                (327usize, 268435454usize),
                (333usize, 268435454usize),
                (303usize, 268435454usize),
                (319usize, 1744830467usize),
                (242usize, 268435454usize),
                (305usize, 1744830467usize),
                (307usize, 268435454usize),
                (323usize, 1744830467usize),
                (246usize, 268435454usize),
                (307usize, 1744830467usize),
                (315usize, 268435454usize),
                (331usize, 1744830467usize),
                (254usize, 268435454usize),
                (311usize, 1744830467usize),
                (238usize, 268435454usize),
                (303usize, 1744830467usize),
                (258usize, 268435454usize),
                (313usize, 1744830467usize),
                (311usize, 268435454usize),
                (327usize, 1744830467usize),
                (317usize, 268435454usize),
                (333usize, 1744830467usize),
                (238usize, 268435454usize),
                (319usize, 1744830467usize),
                (246usize, 268435454usize),
                (323usize, 1744830467usize),
                (262usize, 268435454usize),
                (331usize, 1744830467usize),
                (254usize, 268435454usize),
                (327usize, 1744830467usize),
                (266usize, 268435454usize),
                (333usize, 1744830467usize),
            ];
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
            const VAL_QO: [(usize, usize); 25usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (75usize, 2usize),
                (76usize, 2usize),
                (77usize, 2usize),
                (80usize, 2usize),
                (84usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 40usize] = [
                (320usize, 268435454usize),
                (326usize, 268435454usize),
                (330usize, 268435454usize),
                (314usize, 268435454usize),
                (304usize, 268435454usize),
                (328usize, 268435454usize),
                (316usize, 268435454usize),
                (302usize, 268435454usize),
                (306usize, 268435454usize),
                (324usize, 268435454usize),
                (304usize, 268435454usize),
                (320usize, 1744830467usize),
                (310usize, 268435454usize),
                (326usize, 1744830467usize),
                (314usize, 268435454usize),
                (330usize, 1744830467usize),
                (261usize, 268435454usize),
                (314usize, 1744830467usize),
                (241usize, 268435454usize),
                (304usize, 1744830467usize),
                (312usize, 268435454usize),
                (328usize, 1744830467usize),
                (265usize, 268435454usize),
                (316usize, 1744830467usize),
                (237usize, 268435454usize),
                (302usize, 1744830467usize),
                (245usize, 268435454usize),
                (306usize, 1744830467usize),
                (308usize, 268435454usize),
                (324usize, 1744830467usize),
                (241usize, 268435454usize),
                (320usize, 1744830467usize),
                (253usize, 268435454usize),
                (326usize, 1744830467usize),
                (261usize, 268435454usize),
                (330usize, 1744830467usize),
                (257usize, 268435454usize),
                (328usize, 1744830467usize),
                (249usize, 268435454usize),
                (324usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(103usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 25usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (75usize, 2usize),
                (76usize, 2usize),
                (77usize, 2usize),
                (80usize, 2usize),
                (84usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 40usize] = [
                (321usize, 268435454usize),
                (327usize, 268435454usize),
                (331usize, 268435454usize),
                (315usize, 268435454usize),
                (305usize, 268435454usize),
                (329usize, 268435454usize),
                (317usize, 268435454usize),
                (303usize, 268435454usize),
                (307usize, 268435454usize),
                (325usize, 268435454usize),
                (305usize, 268435454usize),
                (321usize, 1744830467usize),
                (311usize, 268435454usize),
                (327usize, 1744830467usize),
                (315usize, 268435454usize),
                (331usize, 1744830467usize),
                (262usize, 268435454usize),
                (315usize, 1744830467usize),
                (242usize, 268435454usize),
                (305usize, 1744830467usize),
                (313usize, 268435454usize),
                (329usize, 1744830467usize),
                (266usize, 268435454usize),
                (317usize, 1744830467usize),
                (238usize, 268435454usize),
                (303usize, 1744830467usize),
                (246usize, 268435454usize),
                (307usize, 1744830467usize),
                (309usize, 268435454usize),
                (325usize, 1744830467usize),
                (242usize, 268435454usize),
                (321usize, 1744830467usize),
                (254usize, 268435454usize),
                (327usize, 1744830467usize),
                (262usize, 268435454usize),
                (331usize, 1744830467usize),
                (258usize, 268435454usize),
                (329usize, 1744830467usize),
                (250usize, 268435454usize),
                (325usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 25usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (75usize, 2usize),
                (79usize, 2usize),
                (82usize, 2usize),
                (83usize, 2usize),
                (84usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 40usize] = [
                (322usize, 268435454usize),
                (302usize, 268435454usize),
                (308usize, 268435454usize),
                (312usize, 268435454usize),
                (324usize, 268435454usize),
                (316usize, 268435454usize),
                (314usize, 268435454usize),
                (332usize, 268435454usize),
                (328usize, 268435454usize),
                (320usize, 268435454usize),
                (306usize, 268435454usize),
                (322usize, 1744830467usize),
                (237usize, 268435454usize),
                (302usize, 1744830467usize),
                (249usize, 268435454usize),
                (308usize, 1744830467usize),
                (257usize, 268435454usize),
                (312usize, 1744830467usize),
                (308usize, 268435454usize),
                (324usize, 1744830467usize),
                (265usize, 268435454usize),
                (316usize, 1744830467usize),
                (261usize, 268435454usize),
                (314usize, 1744830467usize),
                (316usize, 268435454usize),
                (332usize, 1744830467usize),
                (312usize, 268435454usize),
                (328usize, 1744830467usize),
                (304usize, 268435454usize),
                (320usize, 1744830467usize),
                (245usize, 268435454usize),
                (322usize, 1744830467usize),
                (249usize, 268435454usize),
                (324usize, 1744830467usize),
                (265usize, 268435454usize),
                (332usize, 1744830467usize),
                (257usize, 268435454usize),
                (328usize, 1744830467usize),
                (241usize, 268435454usize),
                (320usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(105usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 25usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (75usize, 2usize),
                (79usize, 2usize),
                (82usize, 2usize),
                (83usize, 2usize),
                (84usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 40usize] = [
                (323usize, 268435454usize),
                (303usize, 268435454usize),
                (309usize, 268435454usize),
                (313usize, 268435454usize),
                (325usize, 268435454usize),
                (317usize, 268435454usize),
                (315usize, 268435454usize),
                (333usize, 268435454usize),
                (329usize, 268435454usize),
                (321usize, 268435454usize),
                (307usize, 268435454usize),
                (323usize, 1744830467usize),
                (238usize, 268435454usize),
                (303usize, 1744830467usize),
                (250usize, 268435454usize),
                (309usize, 1744830467usize),
                (258usize, 268435454usize),
                (313usize, 1744830467usize),
                (309usize, 268435454usize),
                (325usize, 1744830467usize),
                (266usize, 268435454usize),
                (317usize, 1744830467usize),
                (262usize, 268435454usize),
                (315usize, 1744830467usize),
                (317usize, 268435454usize),
                (333usize, 1744830467usize),
                (313usize, 268435454usize),
                (329usize, 1744830467usize),
                (305usize, 268435454usize),
                (321usize, 1744830467usize),
                (246usize, 268435454usize),
                (323usize, 1744830467usize),
                (250usize, 268435454usize),
                (325usize, 1744830467usize),
                (266usize, 268435454usize),
                (333usize, 1744830467usize),
                (258usize, 268435454usize),
                (329usize, 1744830467usize),
                (242usize, 268435454usize),
                (321usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(106usize, 1744830467usize)];
            let val =
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (75usize, 2usize),
                (78usize, 2usize),
                (79usize, 2usize),
                (84usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 38usize] = [
                (324usize, 268435454usize),
                (306usize, 268435454usize),
                (314usize, 268435454usize),
                (322usize, 268435454usize),
                (326usize, 268435454usize),
                (312usize, 268435454usize),
                (308usize, 268435454usize),
                (310usize, 268435454usize),
                (316usize, 268435454usize),
                (330usize, 268435454usize),
                (308usize, 268435454usize),
                (324usize, 1744830467usize),
                (245usize, 268435454usize),
                (306usize, 1744830467usize),
                (261usize, 268435454usize),
                (314usize, 1744830467usize),
                (306usize, 268435454usize),
                (322usize, 1744830467usize),
                (310usize, 268435454usize),
                (326usize, 1744830467usize),
                (257usize, 268435454usize),
                (312usize, 1744830467usize),
                (249usize, 268435454usize),
                (308usize, 1744830467usize),
                (253usize, 268435454usize),
                (310usize, 1744830467usize),
                (265usize, 268435454usize),
                (316usize, 1744830467usize),
                (314usize, 268435454usize),
                (330usize, 1744830467usize),
                (249usize, 268435454usize),
                (324usize, 1744830467usize),
                (245usize, 268435454usize),
                (322usize, 1744830467usize),
                (253usize, 268435454usize),
                (326usize, 1744830467usize),
                (261usize, 268435454usize),
                (330usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(107usize, 1744830467usize)];
            let val =
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (75usize, 2usize),
                (78usize, 2usize),
                (79usize, 2usize),
                (84usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 38usize] = [
                (325usize, 268435454usize),
                (307usize, 268435454usize),
                (315usize, 268435454usize),
                (323usize, 268435454usize),
                (327usize, 268435454usize),
                (313usize, 268435454usize),
                (309usize, 268435454usize),
                (311usize, 268435454usize),
                (317usize, 268435454usize),
                (331usize, 268435454usize),
                (309usize, 268435454usize),
                (325usize, 1744830467usize),
                (246usize, 268435454usize),
                (307usize, 1744830467usize),
                (262usize, 268435454usize),
                (315usize, 1744830467usize),
                (307usize, 268435454usize),
                (323usize, 1744830467usize),
                (311usize, 268435454usize),
                (327usize, 1744830467usize),
                (258usize, 268435454usize),
                (313usize, 1744830467usize),
                (250usize, 268435454usize),
                (309usize, 1744830467usize),
                (254usize, 268435454usize),
                (311usize, 1744830467usize),
                (266usize, 268435454usize),
                (317usize, 1744830467usize),
                (315usize, 268435454usize),
                (331usize, 1744830467usize),
                (250usize, 268435454usize),
                (325usize, 1744830467usize),
                (246usize, 268435454usize),
                (323usize, 1744830467usize),
                (254usize, 268435454usize),
                (327usize, 1744830467usize),
                (262usize, 268435454usize),
                (331usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 1usize] = [(108usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 25usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (75usize, 2usize),
                (76usize, 2usize),
                (80usize, 2usize),
                (81usize, 2usize),
                (82usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 40usize] = [
                (326usize, 268435454usize),
                (324usize, 268435454usize),
                (316usize, 268435454usize),
                (310usize, 268435454usize),
                (314usize, 268435454usize),
                (332usize, 268435454usize),
                (320usize, 268435454usize),
                (318usize, 268435454usize),
                (304usize, 268435454usize),
                (308usize, 268435454usize),
                (310usize, 268435454usize),
                (326usize, 1744830467usize),
                (308usize, 268435454usize),
                (324usize, 1744830467usize),
                (265usize, 268435454usize),
                (316usize, 1744830467usize),
                (253usize, 268435454usize),
                (310usize, 1744830467usize),
                (261usize, 268435454usize),
                (314usize, 1744830467usize),
                (316usize, 268435454usize),
                (332usize, 1744830467usize),
                (304usize, 268435454usize),
                (320usize, 1744830467usize),
                (302usize, 268435454usize),
                (318usize, 1744830467usize),
                (241usize, 268435454usize),
                (304usize, 1744830467usize),
                (249usize, 268435454usize),
                (308usize, 1744830467usize),
                (253usize, 268435454usize),
                (326usize, 1744830467usize),
                (249usize, 268435454usize),
                (324usize, 1744830467usize),
                (265usize, 268435454usize),
                (332usize, 1744830467usize),
                (241usize, 268435454usize),
                (320usize, 1744830467usize),
                (237usize, 268435454usize),
                (318usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 25usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (75usize, 2usize),
                (76usize, 2usize),
                (80usize, 2usize),
                (81usize, 2usize),
                (82usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 40usize] = [
                (327usize, 268435454usize),
                (325usize, 268435454usize),
                (317usize, 268435454usize),
                (311usize, 268435454usize),
                (315usize, 268435454usize),
                (333usize, 268435454usize),
                (321usize, 268435454usize),
                (319usize, 268435454usize),
                (305usize, 268435454usize),
                (309usize, 268435454usize),
                (311usize, 268435454usize),
                (327usize, 1744830467usize),
                (309usize, 268435454usize),
                (325usize, 1744830467usize),
                (266usize, 268435454usize),
                (317usize, 1744830467usize),
                (254usize, 268435454usize),
                (311usize, 1744830467usize),
                (262usize, 268435454usize),
                (315usize, 1744830467usize),
                (317usize, 268435454usize),
                (333usize, 1744830467usize),
                (305usize, 268435454usize),
                (321usize, 1744830467usize),
                (303usize, 268435454usize),
                (319usize, 1744830467usize),
                (242usize, 268435454usize),
                (305usize, 1744830467usize),
                (250usize, 268435454usize),
                (309usize, 1744830467usize),
                (254usize, 268435454usize),
                (327usize, 1744830467usize),
                (250usize, 268435454usize),
                (325usize, 1744830467usize),
                (266usize, 268435454usize),
                (333usize, 1744830467usize),
                (242usize, 268435454usize),
                (321usize, 1744830467usize),
                (238usize, 268435454usize),
                (319usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 24usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (75usize, 2usize),
                (79usize, 2usize),
                (80usize, 2usize),
                (84usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 38usize] = [
                (328usize, 268435454usize),
                (316usize, 268435454usize),
                (304usize, 268435454usize),
                (302usize, 268435454usize),
                (318usize, 268435454usize),
                (330usize, 268435454usize),
                (306usize, 268435454usize),
                (314usize, 268435454usize),
                (310usize, 268435454usize),
                (326usize, 268435454usize),
                (312usize, 268435454usize),
                (328usize, 1744830467usize),
                (265usize, 268435454usize),
                (316usize, 1744830467usize),
                (241usize, 268435454usize),
                (304usize, 1744830467usize),
                (237usize, 268435454usize),
                (302usize, 1744830467usize),
                (302usize, 268435454usize),
                (318usize, 1744830467usize),
                (314usize, 268435454usize),
                (330usize, 1744830467usize),
                (245usize, 268435454usize),
                (306usize, 1744830467usize),
                (261usize, 268435454usize),
                (314usize, 1744830467usize),
                (253usize, 268435454usize),
                (310usize, 1744830467usize),
                (310usize, 268435454usize),
                (326usize, 1744830467usize),
                (257usize, 268435454usize),
                (328usize, 1744830467usize),
                (237usize, 268435454usize),
                (318usize, 1744830467usize),
                (261usize, 268435454usize),
                (330usize, 1744830467usize),
                (253usize, 268435454usize),
                (326usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 24usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (75usize, 2usize),
                (79usize, 2usize),
                (80usize, 2usize),
                (84usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 38usize] = [
                (329usize, 268435454usize),
                (317usize, 268435454usize),
                (305usize, 268435454usize),
                (303usize, 268435454usize),
                (319usize, 268435454usize),
                (331usize, 268435454usize),
                (307usize, 268435454usize),
                (315usize, 268435454usize),
                (311usize, 268435454usize),
                (327usize, 268435454usize),
                (313usize, 268435454usize),
                (329usize, 1744830467usize),
                (266usize, 268435454usize),
                (317usize, 1744830467usize),
                (242usize, 268435454usize),
                (305usize, 1744830467usize),
                (238usize, 268435454usize),
                (303usize, 1744830467usize),
                (303usize, 268435454usize),
                (319usize, 1744830467usize),
                (315usize, 268435454usize),
                (331usize, 1744830467usize),
                (246usize, 268435454usize),
                (307usize, 1744830467usize),
                (262usize, 268435454usize),
                (315usize, 1744830467usize),
                (254usize, 268435454usize),
                (311usize, 1744830467usize),
                (311usize, 268435454usize),
                (327usize, 1744830467usize),
                (258usize, 268435454usize),
                (329usize, 1744830467usize),
                (238usize, 268435454usize),
                (319usize, 1744830467usize),
                (262usize, 268435454usize),
                (331usize, 1744830467usize),
                (254usize, 268435454usize),
                (327usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 26usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (75usize, 2usize),
                (77usize, 2usize),
                (78usize, 2usize),
                (81usize, 2usize),
                (83usize, 2usize),
                (84usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 42usize] = [
                (330usize, 268435454usize),
                (312usize, 268435454usize),
                (320usize, 268435454usize),
                (332usize, 268435454usize),
                (308usize, 268435454usize),
                (304usize, 268435454usize),
                (318usize, 268435454usize),
                (306usize, 268435454usize),
                (322usize, 268435454usize),
                (328usize, 268435454usize),
                (314usize, 268435454usize),
                (330usize, 1744830467usize),
                (257usize, 268435454usize),
                (312usize, 1744830467usize),
                (304usize, 268435454usize),
                (320usize, 1744830467usize),
                (316usize, 268435454usize),
                (332usize, 1744830467usize),
                (249usize, 268435454usize),
                (308usize, 1744830467usize),
                (241usize, 268435454usize),
                (304usize, 1744830467usize),
                (302usize, 268435454usize),
                (318usize, 1744830467usize),
                (245usize, 268435454usize),
                (306usize, 1744830467usize),
                (306usize, 268435454usize),
                (322usize, 1744830467usize),
                (312usize, 268435454usize),
                (328usize, 1744830467usize),
                (261usize, 268435454usize),
                (330usize, 1744830467usize),
                (241usize, 268435454usize),
                (320usize, 1744830467usize),
                (265usize, 268435454usize),
                (332usize, 1744830467usize),
                (237usize, 268435454usize),
                (318usize, 1744830467usize),
                (245usize, 268435454usize),
                (322usize, 1744830467usize),
                (257usize, 268435454usize),
                (328usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 26usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (75usize, 2usize),
                (77usize, 2usize),
                (78usize, 2usize),
                (81usize, 2usize),
                (83usize, 2usize),
                (84usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 42usize] = [
                (331usize, 268435454usize),
                (313usize, 268435454usize),
                (321usize, 268435454usize),
                (333usize, 268435454usize),
                (309usize, 268435454usize),
                (305usize, 268435454usize),
                (319usize, 268435454usize),
                (307usize, 268435454usize),
                (323usize, 268435454usize),
                (329usize, 268435454usize),
                (315usize, 268435454usize),
                (331usize, 1744830467usize),
                (258usize, 268435454usize),
                (313usize, 1744830467usize),
                (305usize, 268435454usize),
                (321usize, 1744830467usize),
                (317usize, 268435454usize),
                (333usize, 1744830467usize),
                (250usize, 268435454usize),
                (309usize, 1744830467usize),
                (242usize, 268435454usize),
                (305usize, 1744830467usize),
                (303usize, 268435454usize),
                (319usize, 1744830467usize),
                (246usize, 268435454usize),
                (307usize, 1744830467usize),
                (307usize, 268435454usize),
                (323usize, 1744830467usize),
                (313usize, 268435454usize),
                (329usize, 1744830467usize),
                (262usize, 268435454usize),
                (331usize, 1744830467usize),
                (242usize, 268435454usize),
                (321usize, 1744830467usize),
                (266usize, 268435454usize),
                (333usize, 1744830467usize),
                (238usize, 268435454usize),
                (319usize, 1744830467usize),
                (246usize, 268435454usize),
                (323usize, 1744830467usize),
                (258usize, 268435454usize),
                (329usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 26usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (75usize, 2usize),
                (78usize, 2usize),
                (79usize, 2usize),
                (80usize, 2usize),
                (81usize, 2usize),
                (82usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 42usize] = [
                (332usize, 268435454usize),
                (308usize, 268435454usize),
                (310usize, 268435454usize),
                (318usize, 268435454usize),
                (328usize, 268435454usize),
                (320usize, 268435454usize),
                (324usize, 268435454usize),
                (322usize, 268435454usize),
                (312usize, 268435454usize),
                (302usize, 268435454usize),
                (316usize, 268435454usize),
                (332usize, 1744830467usize),
                (249usize, 268435454usize),
                (308usize, 1744830467usize),
                (253usize, 268435454usize),
                (310usize, 1744830467usize),
                (302usize, 268435454usize),
                (318usize, 1744830467usize),
                (312usize, 268435454usize),
                (328usize, 1744830467usize),
                (304usize, 268435454usize),
                (320usize, 1744830467usize),
                (308usize, 268435454usize),
                (324usize, 1744830467usize),
                (306usize, 268435454usize),
                (322usize, 1744830467usize),
                (257usize, 268435454usize),
                (312usize, 1744830467usize),
                (237usize, 268435454usize),
                (302usize, 1744830467usize),
                (265usize, 268435454usize),
                (332usize, 1744830467usize),
                (237usize, 268435454usize),
                (318usize, 1744830467usize),
                (257usize, 268435454usize),
                (328usize, 1744830467usize),
                (241usize, 268435454usize),
                (320usize, 1744830467usize),
                (249usize, 268435454usize),
                (324usize, 1744830467usize),
                (245usize, 268435454usize),
                (322usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 26usize] = [
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
                (65usize, 2usize),
                (66usize, 2usize),
                (67usize, 2usize),
                (68usize, 2usize),
                (69usize, 2usize),
                (70usize, 2usize),
                (71usize, 2usize),
                (72usize, 2usize),
                (73usize, 2usize),
                (74usize, 2usize),
                (75usize, 2usize),
                (78usize, 2usize),
                (79usize, 2usize),
                (80usize, 2usize),
                (81usize, 2usize),
                (82usize, 2usize),
            ];
            const VAL_QI: [(usize, usize); 42usize] = [
                (333usize, 268435454usize),
                (309usize, 268435454usize),
                (311usize, 268435454usize),
                (319usize, 268435454usize),
                (329usize, 268435454usize),
                (321usize, 268435454usize),
                (325usize, 268435454usize),
                (323usize, 268435454usize),
                (313usize, 268435454usize),
                (303usize, 268435454usize),
                (317usize, 268435454usize),
                (333usize, 1744830467usize),
                (250usize, 268435454usize),
                (309usize, 1744830467usize),
                (254usize, 268435454usize),
                (311usize, 1744830467usize),
                (303usize, 268435454usize),
                (319usize, 1744830467usize),
                (313usize, 268435454usize),
                (329usize, 1744830467usize),
                (305usize, 268435454usize),
                (321usize, 1744830467usize),
                (309usize, 268435454usize),
                (325usize, 1744830467usize),
                (307usize, 268435454usize),
                (323usize, 1744830467usize),
                (258usize, 268435454usize),
                (313usize, 1744830467usize),
                (238usize, 268435454usize),
                (303usize, 1744830467usize),
                (266usize, 268435454usize),
                (333usize, 1744830467usize),
                (238usize, 268435454usize),
                (319usize, 1744830467usize),
                (258usize, 268435454usize),
                (329usize, 1744830467usize),
                (242usize, 268435454usize),
                (321usize, 1744830467usize),
                (250usize, 268435454usize),
                (325usize, 1744830467usize),
                (246usize, 268435454usize),
                (323usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 1usize] = [(335usize, 268435454usize)];
            let val =
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
                (336usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (143usize, 268435454usize),
                (144usize, 134217455usize),
                (237usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(237usize, 268435454usize), (239usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (146usize, 268435454usize),
                (147usize, 134217455usize),
                (238usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(238usize, 268435454usize), (240usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (149usize, 268435454usize),
                (150usize, 134217455usize),
                (241usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(241usize, 268435454usize), (243usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (152usize, 268435454usize),
                (153usize, 134217455usize),
                (242usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(242usize, 268435454usize), (244usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (155usize, 268435454usize),
                (156usize, 134217455usize),
                (245usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(245usize, 268435454usize), (247usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (158usize, 268435454usize),
                (159usize, 134217455usize),
                (246usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(246usize, 268435454usize), (248usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (161usize, 268435454usize),
                (162usize, 134217455usize),
                (249usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(249usize, 268435454usize), (251usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (164usize, 268435454usize),
                (165usize, 134217455usize),
                (250usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(250usize, 268435454usize), (252usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (167usize, 268435454usize),
                (168usize, 268434910usize),
                (253usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(253usize, 268435454usize), (255usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (170usize, 268435454usize),
                (171usize, 268434910usize),
                (254usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(254usize, 268435454usize), (256usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (173usize, 268435454usize),
                (174usize, 268434910usize),
                (257usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(257usize, 268435454usize), (259usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (176usize, 268435454usize),
                (177usize, 268434910usize),
                (258usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(258usize, 268435454usize), (260usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (179usize, 268435454usize),
                (180usize, 268434910usize),
                (261usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(261usize, 268435454usize), (263usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (182usize, 268435454usize),
                (183usize, 268434910usize),
                (262usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(262usize, 268435454usize), (264usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (185usize, 268435454usize),
                (186usize, 268434910usize),
                (265usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(265usize, 268435454usize), (267usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (189usize, 268435454usize),
                (190usize, 268434910usize),
                (266usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(266usize, 268435454usize), (268usize, 1744830467usize)];
            let val =
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
        for j in 0..1 {
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
        for j in 0..1 {
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
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(117usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(117usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(118usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(118usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(119usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(119usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(120usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(120usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(121usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(121usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(122usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(122usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(123usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(123usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(124usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(124usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(125usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(125usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(126usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(126usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(127usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(127usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(127usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(128usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(128usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(129usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(129usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(130usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(130usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(130usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(131usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(131usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(131usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(132usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(132usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(132usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(133usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(133usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(133usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(134usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(134usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(134usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(137usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(137usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(137usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(138usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(138usize, 268435454usize)];
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
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
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
        for j in 0..1 {
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
        for j in 0..1 {
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
        for j in 0..1 {
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
        for j in 0..1 {
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
    {
        let bc = current_batch;
        field_ops::mul_assign(&mut current_batch, &batch_base);
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(175usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(175usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(178usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(178usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(178usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(181usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(181usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(181usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(184usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(184usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(188usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(188usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(191usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(191usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(192usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(192usize, 268435454usize)];
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
            const VAL_QO: [(usize, usize); 1usize] = [(193usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(193usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(193usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(194usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(194usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(194usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(195usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(195usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(195usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(196usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(196usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(196usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(197usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(197usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(197usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(198usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(198usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(198usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(199usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(199usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(199usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(200usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(200usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(200usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(201usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(201usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(201usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(202usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(202usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(202usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(203usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(203usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(203usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(204usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(204usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(204usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(205usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(205usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(205usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(206usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(206usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(206usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(207usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(207usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(207usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(208usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(208usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(208usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(209usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(209usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(209usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(210usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(210usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(210usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(211usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(211usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(211usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(213usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(213usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(213usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(214usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(214usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(214usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(215usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(215usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(215usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(216usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(216usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(216usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(217usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(217usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(217usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(218usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(218usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(218usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(219usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(219usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(219usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(220usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(220usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(220usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(221usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(221usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(221usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(222usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(222usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(222usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(223usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(223usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(223usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(224usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(224usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(224usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(225usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(225usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(225usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(226usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(226usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(226usize, 1744830467usize)];
            let val =
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
        for j in 0..1 {
            const VAL_QO: [(usize, usize); 1usize] = [(228usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(228usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(228usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(229usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(229usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(229usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(230usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(230usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(230usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(231usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(231usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(231usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(232usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(232usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(232usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(233usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(233usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(233usize, 1744830467usize)];
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
    output_claims: &[BabyBearExt4; 169usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 98usize] = [
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
        (2usize, 67usize, 68usize),
        (1usize, 69usize, 0usize),
        (1usize, 70usize, 0usize),
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
        (1usize, 167usize, 0usize),
        (1usize, 168usize, 0usize),
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 98usize] = [
            (SimpleGateType::Copy, [0usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [1usize, 3usize, 0usize, 0usize]),
            (SimpleGateType::Product, [5usize, 7usize, 0usize, 0usize]),
            (SimpleGateType::Product, [9usize, 11usize, 0usize, 0usize]),
            (SimpleGateType::Product, [13usize, 15usize, 0usize, 0usize]),
            (SimpleGateType::Product, [17usize, 19usize, 0usize, 0usize]),
            (SimpleGateType::Product, [21usize, 23usize, 0usize, 0usize]),
            (SimpleGateType::Product, [25usize, 27usize, 0usize, 0usize]),
            (SimpleGateType::Product, [29usize, 31usize, 0usize, 0usize]),
            (SimpleGateType::Product, [33usize, 35usize, 0usize, 0usize]),
            (SimpleGateType::Product, [37usize, 39usize, 0usize, 0usize]),
            (SimpleGateType::Product, [41usize, 43usize, 0usize, 0usize]),
            (SimpleGateType::Product, [2usize, 4usize, 0usize, 0usize]),
            (SimpleGateType::Product, [6usize, 8usize, 0usize, 0usize]),
            (SimpleGateType::Product, [10usize, 12usize, 0usize, 0usize]),
            (SimpleGateType::Product, [14usize, 16usize, 0usize, 0usize]),
            (SimpleGateType::Product, [18usize, 20usize, 0usize, 0usize]),
            (SimpleGateType::Product, [22usize, 24usize, 0usize, 0usize]),
            (SimpleGateType::Product, [26usize, 28usize, 0usize, 0usize]),
            (SimpleGateType::Product, [30usize, 32usize, 0usize, 0usize]),
            (SimpleGateType::Product, [34usize, 36usize, 0usize, 0usize]),
            (SimpleGateType::Product, [38usize, 40usize, 0usize, 0usize]),
            (SimpleGateType::Product, [42usize, 44usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupUnbalanced,
                [45usize, 46usize, 47usize, 0usize],
            ),
            (
                SimpleGateType::LookupUnbalanced,
                [134usize, 135usize, 136usize, 0usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [132usize, 133usize, 130usize, 131usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [128usize, 129usize, 126usize, 127usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [124usize, 125usize, 122usize, 123usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [120usize, 121usize, 118usize, 119usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [116usize, 117usize, 114usize, 115usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [112usize, 113usize, 110usize, 111usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [108usize, 109usize, 106usize, 107usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [104usize, 105usize, 102usize, 103usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [100usize, 101usize, 98usize, 99usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [96usize, 97usize, 94usize, 95usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [92usize, 93usize, 90usize, 91usize],
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
            (
                SimpleGateType::LookupUnbalanced,
                [327usize, 328usize, 329usize, 0usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [325usize, 326usize, 323usize, 324usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [321usize, 322usize, 319usize, 320usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [317usize, 318usize, 315usize, 316usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [313usize, 314usize, 311usize, 312usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [309usize, 310usize, 307usize, 308usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [305usize, 306usize, 303usize, 304usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [301usize, 302usize, 299usize, 300usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [297usize, 298usize, 295usize, 296usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [293usize, 294usize, 291usize, 292usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [289usize, 290usize, 287usize, 288usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [285usize, 286usize, 283usize, 284usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [281usize, 282usize, 279usize, 280usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [277usize, 278usize, 275usize, 276usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [273usize, 274usize, 271usize, 272usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [269usize, 270usize, 267usize, 268usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [265usize, 266usize, 263usize, 264usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [261usize, 262usize, 259usize, 260usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [257usize, 258usize, 255usize, 256usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [253usize, 254usize, 251usize, 252usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [249usize, 250usize, 247usize, 248usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [245usize, 246usize, 243usize, 244usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [241usize, 242usize, 239usize, 240usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [237usize, 238usize, 235usize, 236usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [233usize, 234usize, 231usize, 232usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [229usize, 230usize, 227usize, 228usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [225usize, 226usize, 223usize, 224usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [221usize, 222usize, 219usize, 220usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [217usize, 218usize, 215usize, 216usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [213usize, 214usize, 211usize, 212usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [209usize, 210usize, 207usize, 208usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [205usize, 206usize, 203usize, 204usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [201usize, 202usize, 199usize, 200usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [197usize, 198usize, 195usize, 196usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [193usize, 194usize, 191usize, 192usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [189usize, 190usize, 187usize, 188usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [185usize, 186usize, 183usize, 184usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [181usize, 182usize, 179usize, 180usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [177usize, 178usize, 175usize, 176usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [173usize, 174usize, 171usize, 172usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [169usize, 170usize, 167usize, 168usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [165usize, 166usize, 163usize, 164usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [161usize, 162usize, 159usize, 160usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [157usize, 158usize, 155usize, 156usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [153usize, 154usize, 151usize, 152usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [149usize, 150usize, 147usize, 148usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [145usize, 146usize, 143usize, 144usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [141usize, 142usize, 139usize, 140usize],
            ),
            (SimpleGateType::Copy, [137usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [138usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 98usize {
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
    output_claims: &[BabyBearExt4; 89usize],
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
        (1usize, 85usize, 0usize),
        (1usize, 86usize, 0usize),
        (1usize, 87usize, 0usize),
        (1usize, 88usize, 0usize),
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 54usize] = [
            (SimpleGateType::Copy, [0usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [1usize, 2usize, 0usize, 0usize]),
            (SimpleGateType::Product, [3usize, 4usize, 0usize, 0usize]),
            (SimpleGateType::Product, [5usize, 6usize, 0usize, 0usize]),
            (SimpleGateType::Product, [7usize, 8usize, 0usize, 0usize]),
            (SimpleGateType::Product, [9usize, 10usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [11usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [12usize, 13usize, 0usize, 0usize]),
            (SimpleGateType::Product, [14usize, 15usize, 0usize, 0usize]),
            (SimpleGateType::Product, [16usize, 17usize, 0usize, 0usize]),
            (SimpleGateType::Product, [18usize, 19usize, 0usize, 0usize]),
            (SimpleGateType::Product, [20usize, 21usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [22usize, 0usize, 0usize, 0usize]),
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
            (
                SimpleGateType::LookupAggregatePair,
                [29usize, 30usize, 27usize, 28usize],
            ),
            (SimpleGateType::Copy, [25usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [26usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupAggregatePair,
                [167usize, 168usize, 165usize, 166usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [163usize, 164usize, 161usize, 162usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [159usize, 160usize, 157usize, 158usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [155usize, 156usize, 153usize, 154usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [151usize, 152usize, 149usize, 150usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [147usize, 148usize, 145usize, 146usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [143usize, 144usize, 141usize, 142usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [139usize, 140usize, 137usize, 138usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [135usize, 136usize, 133usize, 134usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [131usize, 132usize, 129usize, 130usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [127usize, 128usize, 125usize, 126usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [123usize, 124usize, 121usize, 122usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [119usize, 120usize, 117usize, 118usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [115usize, 116usize, 113usize, 114usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [111usize, 112usize, 109usize, 110usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [107usize, 108usize, 105usize, 106usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [103usize, 104usize, 101usize, 102usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [99usize, 100usize, 97usize, 98usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [95usize, 96usize, 93usize, 94usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [91usize, 92usize, 89usize, 90usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [87usize, 88usize, 85usize, 86usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [83usize, 84usize, 81usize, 82usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [79usize, 80usize, 77usize, 78usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [75usize, 76usize, 73usize, 74usize],
            ),
            (SimpleGateType::Copy, [71usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [72usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [23usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [24usize, 0usize, 0usize, 0usize]),
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
    acc
}
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_3_compute_claim(
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
        (1usize, 43usize, 0usize),
        (1usize, 44usize, 0usize),
        (1usize, 45usize, 0usize),
        (1usize, 46usize, 0usize),
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 29usize] = [
            (SimpleGateType::Copy, [0usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Product, [1usize, 2usize, 0usize, 0usize]),
            (SimpleGateType::Product, [3usize, 4usize, 0usize, 0usize]),
            (SimpleGateType::Product, [5usize, 6usize, 0usize, 0usize]),
            (SimpleGateType::Product, [7usize, 8usize, 0usize, 0usize]),
            (SimpleGateType::Product, [9usize, 10usize, 0usize, 0usize]),
            (SimpleGateType::Product, [11usize, 12usize, 0usize, 0usize]),
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
            (SimpleGateType::Copy, [87usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [88usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 29usize {
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
    output_claims: &[BabyBearExt4; 27usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 18usize] = [
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
        (1usize, 25usize, 0usize),
        (1usize, 26usize, 0usize),
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 18usize] = [
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
            (SimpleGateType::Copy, [19usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [20usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [45usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [46usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 18usize {
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
    output_claims: &[BabyBearExt4; 17usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 13usize] = [
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
        (1usize, 15usize, 0usize),
        (1usize, 16usize, 0usize),
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 13usize] = [
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
            (SimpleGateType::Copy, [25usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [26usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 13usize {
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
unsafe fn layer_6_compute_claim(
    output_claims: &[BabyBearExt4; 10usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 7usize] = [
        (1usize, 0usize, 0usize),
        (1usize, 1usize, 0usize),
        (2usize, 2usize, 3usize),
        (2usize, 4usize, 5usize),
        (2usize, 6usize, 7usize),
        (1usize, 8usize, 0usize),
        (1usize, 9usize, 0usize),
    ];
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_6_final_step_accumulator(
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 7usize] = [
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
                [13usize, 14usize, 11usize, 12usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [9usize, 10usize, 7usize, 8usize],
            ),
            (SimpleGateType::Copy, [15usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [16usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 7usize {
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
unsafe fn layer_7_compute_claim(
    output_claims: &[BabyBearExt4; 8usize],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 7usize] = [
        (2usize, 0usize, 1usize),
        (1usize, 2usize, 0usize),
        (1usize, 3usize, 0usize),
        (1usize, 4usize, 0usize),
        (1usize, 5usize, 0usize),
        (1usize, 6usize, 0usize),
        (1usize, 7usize, 0usize),
    ];
    super::common::compute_claim(output_claims, &DESCS, batch_base)
}
#[inline(always)]
#[allow(unused_variables, unused_mut, unused_unsafe)]
unsafe fn layer_7_final_step_accumulator(
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 7usize] = [
            (
                SimpleGateType::LookupAggregatePair,
                [6usize, 7usize, 4usize, 5usize],
            ),
            (SimpleGateType::Copy, [0usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [1usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [8usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [9usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [2usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [3usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 7usize {
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
        let pt = state.prev_point.get_unchecked(..20usize);
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
        while k < 20usize {
            let mut t: BabyBearExt4 = BabyBearExt4::ONE;
            let p = pt.get_unchecked(k);
            field_ops::sub_assign(&mut t, &*p);
            field_ops::mul_assign(&mut result, &t);
            k += 1;
        }
        if result != *state.prev_claims.get_unchecked(770usize) {
            return Err(E::gkr_virtual_setup_eval_mismatch(770usize));
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
        let pt = state.prev_point.get_unchecked(..20usize);
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
        while k < 20usize {
            let mut t: BabyBearExt4 = BabyBearExt4::ONE;
            let p = pt.get_unchecked(k);
            field_ops::sub_assign(&mut t, &*p);
            field_ops::mul_assign(&mut result, &t);
            k += 1;
        }
        if result != *state.prev_claims.get_unchecked(771usize) {
            return Err(E::gkr_virtual_setup_eval_mismatch(771usize));
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
        const DIM_REDUCE_INDICES_8: [usize; 8usize] = [
            2usize, 3usize, 4usize, 5usize, 6usize, 7usize, 0usize, 1usize,
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
            let initial_claim = layer_7_compute_claim(
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
            let fc_len = 20usize;
            const NUM_AT_POINT_EVALS: usize = 10usize;
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
                let f = layer_7_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                    &initial_transcript.inits_and_teardowns_top_bits,
                );
                verify_final_step_check::<E>(f[0], final_eq_prefactor, final_claim, 7usize)?;
            }
            ts.commit(&mut eval_buf, data_words);
            let next_batching = draw_single_field_el(ts);
            fold_standard_claims::<10usize, GKR_ADDRS, GKR_EVAL_BUF>(
                &eval_buf,
                &mut state.prev_claims,
            );
            state.batching_challenge = next_batching;
            state.prev_point_len = fc_len;
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR MAIN LAYER 7");
        }
        {
            let initial_claim = layer_6_compute_claim(
                state.prev_claims.as_array::<10usize>(),
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
            let fc_len = 20usize;
            const NUM_AT_POINT_EVALS: usize = 17usize;
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
                let f = layer_6_final_step_accumulator(
                    evals,
                    state.batching_challenge,
                    lookup_additive_challenge,
                    lookup_alpha,
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
                    address_high_bits_shift,
                    &initial_transcript.inits_and_teardowns_top_bits,
                );
                verify_final_step_check::<E>(f[0], final_eq_prefactor, final_claim, 6usize)?;
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
            verifier_common::stats::log("GKR MAIN LAYER 6");
        }
        {
            let initial_claim = layer_5_compute_claim(
                state.prev_claims.as_array::<17usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 20usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    5usize,
                    nd_source,
                )?;
            let fc_len = 20usize;
            const NUM_AT_POINT_EVALS: usize = 27usize;
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
            fold_standard_claims::<27usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<27usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 20usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    4usize,
                    nd_source,
                )?;
            let fc_len = 20usize;
            const NUM_AT_POINT_EVALS: usize = 47usize;
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
            fold_standard_claims::<47usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<47usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 20usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    3usize,
                    nd_source,
                )?;
            let fc_len = 20usize;
            const NUM_AT_POINT_EVALS: usize = 89usize;
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
            fold_standard_claims::<89usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<89usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 20usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    2usize,
                    nd_source,
                )?;
            let fc_len = 20usize;
            const NUM_AT_POINT_EVALS: usize = 169usize;
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
            fold_standard_claims::<169usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<169usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 20usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    1usize,
                    nd_source,
                )?;
            let fc_len = 20usize;
            const NUM_AT_POINT_EVALS: usize = 330usize;
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
            fold_standard_claims::<330usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<330usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 20usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    0usize,
                    nd_source,
                )?;
            let fc_len = 20usize;
            const NUM_AT_POINT_EVALS: usize = 710usize;
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
            const NUM_EXTRA_EVALS: usize = 430usize;
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
                const LAYOUT_KIND: [usize; 1140usize] = [
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize,
                    1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize,
                    0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize,
                    1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize,
                    0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 1usize, 1usize,
                    1usize, 1usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize,
                    1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize,
                    0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 1usize, 1usize,
                    1usize, 1usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize,
                    1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize,
                    0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 1usize, 1usize,
                    1usize, 1usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize,
                    1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 1usize, 0usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    1usize, 1usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 1usize, 1usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    1usize, 1usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 1usize, 1usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    1usize, 1usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 1usize, 1usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 1usize, 1usize, 1usize, 0usize,
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
                    0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 0usize, 1usize, 1usize, 0usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 1usize, 0usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 0usize, 1usize, 1usize, 0usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 1usize, 0usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 0usize, 1usize, 1usize, 0usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 1usize, 0usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 0usize, 1usize, 1usize, 0usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 1usize, 0usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 0usize, 1usize, 1usize, 0usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 0usize, 1usize, 1usize, 0usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 0usize, 1usize, 1usize, 0usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 0usize, 1usize, 1usize, 0usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 1usize, 1usize,
                    1usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize,
                    1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 1usize, 1usize,
                    1usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize,
                    1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 1usize, 1usize,
                    1usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize,
                    1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
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
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                ];
                const LAYOUT_POS: [usize; 1140usize] = [
                    302usize, 303usize, 304usize, 305usize, 306usize, 307usize, 237usize, 238usize,
                    239usize, 240usize, 308usize, 309usize, 241usize, 242usize, 243usize, 244usize,
                    310usize, 311usize, 245usize, 246usize, 247usize, 248usize, 312usize, 313usize,
                    249usize, 250usize, 251usize, 252usize, 314usize, 315usize, 253usize, 254usize,
                    255usize, 256usize, 316usize, 317usize, 257usize, 258usize, 259usize, 260usize,
                    318usize, 319usize, 261usize, 262usize, 263usize, 264usize, 320usize, 321usize,
                    265usize, 266usize, 267usize, 268usize, 322usize, 323usize, 269usize, 270usize,
                    324usize, 325usize, 326usize, 327usize, 271usize, 272usize, 328usize, 329usize,
                    330usize, 331usize, 273usize, 274usize, 332usize, 333usize, 334usize, 335usize,
                    275usize, 276usize, 336usize, 337usize, 338usize, 339usize, 277usize, 278usize,
                    340usize, 341usize, 342usize, 343usize, 279usize, 280usize, 344usize, 345usize,
                    346usize, 347usize, 281usize, 282usize, 348usize, 349usize, 350usize, 351usize,
                    283usize, 284usize, 352usize, 353usize, 354usize, 355usize, 285usize, 286usize,
                    356usize, 357usize, 358usize, 359usize, 287usize, 288usize, 360usize, 361usize,
                    362usize, 363usize, 289usize, 290usize, 364usize, 365usize, 366usize, 367usize,
                    291usize, 292usize, 368usize, 369usize, 370usize, 371usize, 293usize, 294usize,
                    372usize, 373usize, 374usize, 375usize, 295usize, 296usize, 376usize, 377usize,
                    378usize, 379usize, 297usize, 298usize, 380usize, 381usize, 382usize, 383usize,
                    299usize, 300usize, 384usize, 301usize, 385usize, 386usize, 387usize, 388usize,
                    389usize, 390usize, 302usize, 303usize, 391usize, 392usize, 304usize, 305usize,
                    393usize, 394usize, 306usize, 307usize, 395usize, 396usize, 308usize, 309usize,
                    397usize, 398usize, 310usize, 311usize, 399usize, 400usize, 312usize, 313usize,
                    401usize, 402usize, 314usize, 315usize, 403usize, 404usize, 316usize, 317usize,
                    405usize, 406usize, 318usize, 319usize, 407usize, 408usize, 320usize, 321usize,
                    409usize, 410usize, 322usize, 323usize, 411usize, 412usize, 324usize, 325usize,
                    413usize, 414usize, 326usize, 327usize, 415usize, 416usize, 328usize, 329usize,
                    417usize, 418usize, 330usize, 331usize, 419usize, 420usize, 332usize, 333usize,
                    421usize, 422usize, 423usize, 334usize, 335usize, 336usize, 337usize, 338usize,
                    339usize, 0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
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
                    113usize, 114usize, 115usize, 116usize, 0usize, 1usize, 2usize, 3usize, 4usize,
                    5usize, 6usize, 7usize, 8usize, 9usize, 10usize, 11usize, 117usize, 12usize,
                    13usize, 118usize, 14usize, 15usize, 16usize, 17usize, 18usize, 19usize,
                    20usize, 21usize, 22usize, 23usize, 24usize, 25usize, 26usize, 27usize,
                    28usize, 29usize, 30usize, 119usize, 31usize, 120usize, 32usize, 33usize,
                    34usize, 35usize, 36usize, 37usize, 38usize, 39usize, 40usize, 41usize,
                    42usize, 43usize, 44usize, 45usize, 46usize, 47usize, 121usize, 48usize,
                    49usize, 122usize, 50usize, 51usize, 52usize, 53usize, 54usize, 55usize,
                    56usize, 57usize, 58usize, 59usize, 60usize, 61usize, 62usize, 63usize,
                    64usize, 65usize, 66usize, 123usize, 67usize, 124usize, 68usize, 69usize,
                    70usize, 71usize, 72usize, 73usize, 74usize, 75usize, 76usize, 77usize,
                    78usize, 79usize, 80usize, 81usize, 82usize, 83usize, 125usize, 84usize,
                    85usize, 126usize, 86usize, 87usize, 88usize, 89usize, 90usize, 91usize,
                    92usize, 93usize, 94usize, 95usize, 96usize, 97usize, 98usize, 99usize,
                    100usize, 101usize, 102usize, 127usize, 103usize, 128usize, 104usize, 105usize,
                    106usize, 107usize, 108usize, 109usize, 110usize, 111usize, 112usize, 113usize,
                    114usize, 115usize, 116usize, 117usize, 118usize, 119usize, 129usize, 120usize,
                    121usize, 130usize, 122usize, 123usize, 124usize, 125usize, 126usize, 127usize,
                    128usize, 129usize, 130usize, 131usize, 132usize, 133usize, 134usize, 135usize,
                    136usize, 137usize, 138usize, 131usize, 139usize, 132usize, 140usize, 141usize,
                    142usize, 143usize, 144usize, 145usize, 146usize, 147usize, 148usize, 149usize,
                    150usize, 151usize, 152usize, 153usize, 133usize, 154usize, 155usize, 134usize,
                    156usize, 157usize, 158usize, 159usize, 160usize, 161usize, 162usize, 163usize,
                    164usize, 165usize, 166usize, 135usize, 167usize, 168usize, 169usize, 170usize,
                    171usize, 172usize, 173usize, 174usize, 175usize, 176usize, 177usize, 178usize,
                    179usize, 180usize, 136usize, 181usize, 182usize, 137usize, 183usize, 184usize,
                    185usize, 186usize, 187usize, 188usize, 189usize, 190usize, 191usize, 192usize,
                    193usize, 194usize, 195usize, 196usize, 197usize, 198usize, 199usize, 200usize,
                    201usize, 202usize, 203usize, 204usize, 205usize, 206usize, 207usize, 208usize,
                    138usize, 209usize, 210usize, 139usize, 211usize, 212usize, 213usize, 214usize,
                    215usize, 216usize, 217usize, 218usize, 219usize, 220usize, 221usize, 222usize,
                    223usize, 224usize, 225usize, 226usize, 227usize, 228usize, 229usize, 230usize,
                    231usize, 232usize, 233usize, 234usize, 235usize, 236usize, 140usize, 237usize,
                    238usize, 141usize, 239usize, 240usize, 241usize, 242usize, 243usize, 244usize,
                    245usize, 246usize, 247usize, 248usize, 249usize, 250usize, 251usize, 252usize,
                    253usize, 254usize, 255usize, 256usize, 257usize, 142usize, 143usize, 144usize,
                    258usize, 259usize, 260usize, 145usize, 146usize, 147usize, 261usize, 262usize,
                    263usize, 148usize, 149usize, 150usize, 264usize, 265usize, 266usize, 151usize,
                    152usize, 153usize, 267usize, 268usize, 269usize, 154usize, 155usize, 156usize,
                    270usize, 271usize, 272usize, 157usize, 158usize, 159usize, 273usize, 274usize,
                    275usize, 160usize, 161usize, 162usize, 276usize, 277usize, 278usize, 163usize,
                    164usize, 165usize, 279usize, 280usize, 281usize, 166usize, 167usize, 168usize,
                    282usize, 283usize, 284usize, 169usize, 170usize, 171usize, 285usize, 286usize,
                    287usize, 172usize, 173usize, 174usize, 288usize, 289usize, 290usize, 175usize,
                    176usize, 177usize, 291usize, 292usize, 293usize, 178usize, 179usize, 180usize,
                    294usize, 295usize, 296usize, 181usize, 182usize, 183usize, 297usize, 298usize,
                    299usize, 184usize, 185usize, 186usize, 300usize, 301usize, 187usize, 188usize,
                    189usize, 190usize, 191usize, 192usize, 193usize, 194usize, 195usize, 196usize,
                    197usize, 198usize, 199usize, 200usize, 201usize, 202usize, 203usize, 204usize,
                    205usize, 206usize, 207usize, 208usize, 209usize, 210usize, 211usize, 212usize,
                    213usize, 214usize, 215usize, 216usize, 217usize, 218usize, 219usize, 220usize,
                    221usize, 222usize, 223usize, 224usize, 225usize, 226usize, 227usize, 228usize,
                    229usize, 230usize, 231usize, 232usize, 233usize, 234usize, 235usize, 236usize,
                    424usize, 425usize, 426usize, 427usize, 428usize, 429usize, 340usize, 341usize,
                    342usize, 343usize, 344usize, 345usize, 346usize, 347usize, 348usize, 349usize,
                    350usize, 351usize, 352usize, 353usize, 354usize, 355usize, 356usize, 357usize,
                    358usize, 359usize, 360usize, 361usize, 362usize, 363usize, 364usize, 365usize,
                    366usize, 367usize, 368usize, 369usize, 370usize, 371usize, 372usize, 373usize,
                    374usize, 375usize, 376usize, 377usize, 378usize, 379usize, 380usize, 381usize,
                    382usize, 383usize, 384usize, 385usize, 386usize, 387usize, 388usize, 389usize,
                    390usize, 391usize, 392usize, 393usize, 394usize, 395usize, 396usize, 397usize,
                    398usize, 399usize, 400usize, 401usize, 402usize, 403usize, 404usize, 405usize,
                    406usize, 407usize, 408usize, 409usize, 410usize, 411usize, 412usize, 413usize,
                    414usize, 415usize, 416usize, 417usize, 418usize, 419usize, 420usize, 421usize,
                    422usize, 423usize, 424usize, 425usize, 426usize, 427usize, 428usize, 429usize,
                    430usize, 431usize, 432usize, 433usize, 434usize, 435usize, 436usize, 437usize,
                    438usize, 439usize, 440usize, 441usize, 442usize, 443usize, 444usize, 445usize,
                    446usize, 447usize, 448usize, 449usize, 450usize, 451usize, 452usize, 453usize,
                    454usize, 455usize, 456usize, 457usize, 458usize, 459usize, 460usize, 461usize,
                    462usize, 463usize, 464usize, 465usize, 466usize, 467usize, 468usize, 469usize,
                    470usize, 471usize, 472usize, 473usize, 474usize, 475usize, 476usize, 477usize,
                    478usize, 479usize, 480usize, 481usize, 482usize, 483usize, 484usize, 485usize,
                    486usize, 487usize, 488usize, 489usize, 490usize, 491usize, 492usize, 493usize,
                    494usize, 495usize, 496usize, 497usize, 498usize, 499usize, 500usize, 501usize,
                    502usize, 503usize, 504usize, 505usize, 506usize, 507usize, 508usize, 509usize,
                    510usize, 511usize, 512usize, 513usize, 514usize, 515usize, 516usize, 517usize,
                    518usize, 519usize, 520usize, 521usize, 522usize, 523usize, 524usize, 525usize,
                    526usize, 527usize, 528usize, 529usize, 530usize, 531usize, 532usize, 533usize,
                    534usize, 535usize, 536usize, 537usize, 538usize, 539usize, 540usize, 541usize,
                    542usize, 543usize, 544usize, 545usize, 546usize, 547usize, 548usize, 549usize,
                    550usize, 551usize, 552usize, 553usize, 554usize, 555usize, 556usize, 557usize,
                    558usize, 559usize, 560usize, 561usize, 562usize, 563usize, 564usize, 565usize,
                    566usize, 567usize, 568usize, 569usize, 570usize, 571usize, 572usize, 573usize,
                    574usize, 575usize, 576usize, 577usize, 578usize, 579usize, 580usize, 581usize,
                    582usize, 583usize, 584usize, 585usize, 586usize, 587usize, 588usize, 589usize,
                    590usize, 591usize, 592usize, 593usize, 594usize, 595usize, 596usize, 597usize,
                    598usize, 599usize, 600usize, 601usize, 602usize, 603usize, 604usize, 605usize,
                    606usize, 607usize, 608usize, 609usize, 610usize, 611usize, 612usize, 613usize,
                    614usize, 615usize, 616usize, 617usize, 618usize, 619usize, 620usize, 621usize,
                    622usize, 623usize, 624usize, 625usize, 626usize, 627usize, 628usize, 629usize,
                    630usize, 631usize, 632usize, 633usize, 634usize, 635usize, 636usize, 637usize,
                    638usize, 639usize, 640usize, 641usize, 642usize, 643usize, 644usize, 645usize,
                    646usize, 647usize, 648usize, 649usize, 650usize, 651usize, 652usize, 653usize,
                    654usize, 655usize, 656usize, 657usize, 658usize, 659usize, 660usize, 661usize,
                    662usize, 663usize, 664usize, 665usize, 666usize, 667usize, 668usize, 669usize,
                    670usize, 671usize, 672usize, 673usize, 674usize, 675usize, 676usize, 677usize,
                    678usize, 679usize, 680usize, 681usize, 682usize, 683usize, 684usize, 685usize,
                    686usize, 687usize, 688usize, 689usize, 690usize, 691usize, 692usize, 693usize,
                    694usize, 695usize, 696usize, 697usize, 698usize, 699usize, 700usize, 701usize,
                    702usize, 703usize, 704usize, 705usize, 706usize, 707usize, 708usize, 709usize,
                ];
                let mut i = 0usize;
                while i < 1140usize {
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
                const SC_DESCS: [(usize, u32, usize, usize); 88usize] = [
                    (860usize, 0u32, 0usize, 1usize),
                    (861usize, 0u32, 1usize, 1usize),
                    (862usize, 1476395013u32, 2usize, 3usize),
                    (863usize, 133099247u32, 5usize, 3usize),
                    (864usize, 1476395013u32, 8usize, 3usize),
                    (865usize, 133099247u32, 11usize, 3usize),
                    (866usize, 1476395013u32, 14usize, 3usize),
                    (867usize, 133099247u32, 17usize, 3usize),
                    (868usize, 1476395013u32, 20usize, 3usize),
                    (869usize, 133099247u32, 23usize, 3usize),
                    (870usize, 1476395013u32, 26usize, 3usize),
                    (871usize, 133099247u32, 29usize, 3usize),
                    (872usize, 1476395013u32, 32usize, 3usize),
                    (873usize, 133099247u32, 35usize, 3usize),
                    (874usize, 1476395013u32, 38usize, 3usize),
                    (875usize, 133099247u32, 41usize, 3usize),
                    (876usize, 1476395013u32, 44usize, 3usize),
                    (877usize, 133099247u32, 47usize, 3usize),
                    (878usize, 1476395013u32, 50usize, 3usize),
                    (879usize, 133099247u32, 53usize, 3usize),
                    (880usize, 1476395013u32, 56usize, 3usize),
                    (881usize, 133099247u32, 59usize, 3usize),
                    (882usize, 1476395013u32, 62usize, 3usize),
                    (883usize, 133099247u32, 65usize, 3usize),
                    (884usize, 1476395013u32, 68usize, 3usize),
                    (885usize, 133099247u32, 71usize, 3usize),
                    (886usize, 1476395013u32, 74usize, 3usize),
                    (887usize, 133099247u32, 77usize, 3usize),
                    (888usize, 1476395013u32, 80usize, 3usize),
                    (889usize, 133099247u32, 83usize, 3usize),
                    (890usize, 1476395013u32, 86usize, 3usize),
                    (891usize, 133099247u32, 89usize, 3usize),
                    (892usize, 1476395013u32, 92usize, 3usize),
                    (893usize, 133099247u32, 95usize, 3usize),
                    (894usize, 1476395013u32, 98usize, 3usize),
                    (895usize, 133099247u32, 101usize, 3usize),
                    (896usize, 1476395013u32, 104usize, 3usize),
                    (897usize, 133099247u32, 107usize, 3usize),
                    (898usize, 1476395013u32, 110usize, 3usize),
                    (899usize, 133099247u32, 113usize, 3usize),
                    (900usize, 1476395013u32, 116usize, 3usize),
                    (901usize, 133099247u32, 119usize, 3usize),
                    (902usize, 1476395013u32, 122usize, 3usize),
                    (903usize, 133099247u32, 125usize, 3usize),
                    (904usize, 1476395013u32, 128usize, 3usize),
                    (905usize, 133099247u32, 131usize, 3usize),
                    (906usize, 1476395013u32, 134usize, 3usize),
                    (907usize, 133099247u32, 137usize, 3usize),
                    (908usize, 1476395013u32, 140usize, 3usize),
                    (909usize, 133099247u32, 143usize, 3usize),
                    (910usize, 1476395013u32, 146usize, 3usize),
                    (911usize, 133099247u32, 149usize, 3usize),
                    (912usize, 1476395013u32, 152usize, 3usize),
                    (913usize, 133099247u32, 155usize, 3usize),
                    (914usize, 1476395013u32, 158usize, 3usize),
                    (915usize, 133099247u32, 161usize, 3usize),
                    (916usize, 1476395013u32, 164usize, 3usize),
                    (917usize, 133099247u32, 167usize, 3usize),
                    (918usize, 1476395013u32, 170usize, 3usize),
                    (919usize, 133099247u32, 173usize, 3usize),
                    (920usize, 1476395013u32, 176usize, 3usize),
                    (921usize, 133099247u32, 179usize, 3usize),
                    (922usize, 1476395013u32, 182usize, 3usize),
                    (923usize, 133099247u32, 185usize, 3usize),
                    (924usize, 1476395013u32, 188usize, 3usize),
                    (925usize, 133099247u32, 191usize, 3usize),
                    (926usize, 1476395013u32, 194usize, 3usize),
                    (927usize, 133099247u32, 197usize, 3usize),
                    (928usize, 1476395013u32, 200usize, 3usize),
                    (929usize, 133099247u32, 203usize, 3usize),
                    (930usize, 1476395013u32, 206usize, 3usize),
                    (931usize, 133099247u32, 209usize, 3usize),
                    (932usize, 1476395013u32, 212usize, 3usize),
                    (933usize, 133099247u32, 215usize, 3usize),
                    (934usize, 1476395013u32, 218usize, 3usize),
                    (935usize, 133099247u32, 221usize, 3usize),
                    (936usize, 1476395013u32, 224usize, 3usize),
                    (937usize, 133099247u32, 227usize, 3usize),
                    (938usize, 1476395013u32, 230usize, 3usize),
                    (939usize, 133099247u32, 233usize, 3usize),
                    (940usize, 1476395013u32, 236usize, 3usize),
                    (941usize, 133099247u32, 239usize, 3usize),
                    (942usize, 1476395013u32, 242usize, 3usize),
                    (943usize, 133099247u32, 245usize, 3usize),
                    (944usize, 1476395013u32, 248usize, 3usize),
                    (945usize, 133099247u32, 251usize, 3usize),
                    (946usize, 1476395013u32, 254usize, 3usize),
                    (947usize, 133099247u32, 257usize, 3usize),
                ];
                const SC_TERMS: [(u32, usize); 260usize] = [
                    (33554432u32, 2usize),
                    (67108864u32, 150usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 0usize),
                    (133099247u32, 718usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 1usize),
                    (1744830467u32, 718usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 4usize),
                    (133099247u32, 719usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 5usize),
                    (1744830467u32, 719usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 10usize),
                    (133099247u32, 720usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 11usize),
                    (1744830467u32, 720usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 16usize),
                    (133099247u32, 721usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 17usize),
                    (1744830467u32, 721usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 22usize),
                    (133099247u32, 722usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 23usize),
                    (1744830467u32, 722usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 28usize),
                    (133099247u32, 723usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 29usize),
                    (1744830467u32, 723usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 34usize),
                    (133099247u32, 724usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 35usize),
                    (1744830467u32, 724usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 40usize),
                    (133099247u32, 725usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 41usize),
                    (1744830467u32, 725usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 46usize),
                    (133099247u32, 726usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 47usize),
                    (1744830467u32, 726usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 52usize),
                    (133099247u32, 727usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 53usize),
                    (1744830467u32, 727usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 58usize),
                    (133099247u32, 728usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 59usize),
                    (1744830467u32, 728usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 64usize),
                    (133099247u32, 729usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 65usize),
                    (1744830467u32, 729usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 70usize),
                    (133099247u32, 730usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 71usize),
                    (1744830467u32, 730usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 76usize),
                    (133099247u32, 731usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 77usize),
                    (1744830467u32, 731usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 82usize),
                    (133099247u32, 732usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 83usize),
                    (1744830467u32, 732usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 88usize),
                    (133099247u32, 733usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 89usize),
                    (1744830467u32, 733usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 94usize),
                    (133099247u32, 734usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 95usize),
                    (1744830467u32, 734usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 100usize),
                    (133099247u32, 735usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 101usize),
                    (1744830467u32, 735usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 106usize),
                    (133099247u32, 736usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 107usize),
                    (1744830467u32, 736usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 112usize),
                    (133099247u32, 737usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 113usize),
                    (1744830467u32, 737usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 118usize),
                    (133099247u32, 738usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 119usize),
                    (1744830467u32, 738usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 124usize),
                    (133099247u32, 739usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 125usize),
                    (1744830467u32, 739usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 130usize),
                    (133099247u32, 740usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 131usize),
                    (1744830467u32, 740usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 136usize),
                    (133099247u32, 741usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 137usize),
                    (1744830467u32, 741usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 142usize),
                    (133099247u32, 742usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 143usize),
                    (1744830467u32, 742usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 148usize),
                    (133099247u32, 743usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 149usize),
                    (1744830467u32, 743usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 152usize),
                    (133099247u32, 744usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 153usize),
                    (1744830467u32, 744usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 156usize),
                    (133099247u32, 745usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 157usize),
                    (1744830467u32, 745usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 160usize),
                    (133099247u32, 746usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 161usize),
                    (1744830467u32, 746usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 164usize),
                    (133099247u32, 747usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 165usize),
                    (1744830467u32, 747usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 168usize),
                    (133099247u32, 748usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 169usize),
                    (1744830467u32, 748usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 172usize),
                    (133099247u32, 749usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 173usize),
                    (1744830467u32, 749usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 176usize),
                    (133099247u32, 750usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 177usize),
                    (1744830467u32, 750usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 180usize),
                    (133099247u32, 751usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 181usize),
                    (1744830467u32, 751usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 184usize),
                    (133099247u32, 752usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 185usize),
                    (1744830467u32, 752usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 188usize),
                    (133099247u32, 753usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 189usize),
                    (1744830467u32, 753usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 192usize),
                    (133099247u32, 754usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 193usize),
                    (1744830467u32, 754usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 196usize),
                    (133099247u32, 755usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 197usize),
                    (1744830467u32, 755usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 200usize),
                    (133099247u32, 756usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 201usize),
                    (1744830467u32, 756usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 204usize),
                    (133099247u32, 757usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 205usize),
                    (1744830467u32, 757usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 208usize),
                    (133099247u32, 758usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 209usize),
                    (1744830467u32, 758usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 212usize),
                    (133099247u32, 759usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 213usize),
                    (1744830467u32, 759usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 216usize),
                    (133099247u32, 760usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 217usize),
                    (1744830467u32, 760usize),
                ];
                let mut _sc = 0;
                while _sc < 88usize {
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
                const VL_DESCS: [(usize, usize, usize); 191usize] = [
                    (948usize, 0usize, 6usize),
                    (950usize, 6usize, 6usize),
                    (951usize, 12usize, 6usize),
                    (952usize, 18usize, 6usize),
                    (953usize, 24usize, 6usize),
                    (954usize, 30usize, 6usize),
                    (955usize, 36usize, 6usize),
                    (956usize, 42usize, 6usize),
                    (957usize, 48usize, 6usize),
                    (958usize, 54usize, 6usize),
                    (959usize, 60usize, 6usize),
                    (960usize, 66usize, 6usize),
                    (961usize, 72usize, 6usize),
                    (962usize, 78usize, 6usize),
                    (963usize, 84usize, 6usize),
                    (964usize, 90usize, 6usize),
                    (965usize, 96usize, 6usize),
                    (966usize, 102usize, 6usize),
                    (967usize, 108usize, 6usize),
                    (968usize, 114usize, 6usize),
                    (969usize, 120usize, 6usize),
                    (970usize, 126usize, 6usize),
                    (971usize, 132usize, 6usize),
                    (972usize, 138usize, 6usize),
                    (973usize, 144usize, 6usize),
                    (974usize, 150usize, 6usize),
                    (975usize, 156usize, 6usize),
                    (976usize, 162usize, 6usize),
                    (977usize, 168usize, 6usize),
                    (978usize, 174usize, 6usize),
                    (979usize, 180usize, 6usize),
                    (980usize, 186usize, 6usize),
                    (981usize, 192usize, 6usize),
                    (982usize, 198usize, 6usize),
                    (983usize, 204usize, 6usize),
                    (984usize, 210usize, 6usize),
                    (985usize, 216usize, 6usize),
                    (986usize, 222usize, 6usize),
                    (987usize, 228usize, 6usize),
                    (988usize, 234usize, 6usize),
                    (989usize, 240usize, 6usize),
                    (990usize, 246usize, 6usize),
                    (991usize, 252usize, 6usize),
                    (992usize, 258usize, 6usize),
                    (993usize, 264usize, 6usize),
                    (994usize, 270usize, 6usize),
                    (995usize, 276usize, 6usize),
                    (996usize, 282usize, 6usize),
                    (997usize, 288usize, 6usize),
                    (998usize, 294usize, 6usize),
                    (999usize, 300usize, 6usize),
                    (1000usize, 306usize, 6usize),
                    (1001usize, 312usize, 6usize),
                    (1002usize, 318usize, 6usize),
                    (1003usize, 324usize, 6usize),
                    (1004usize, 330usize, 6usize),
                    (1005usize, 336usize, 6usize),
                    (1006usize, 342usize, 6usize),
                    (1007usize, 348usize, 6usize),
                    (1008usize, 354usize, 6usize),
                    (1009usize, 360usize, 6usize),
                    (1010usize, 366usize, 6usize),
                    (1011usize, 372usize, 6usize),
                    (1012usize, 378usize, 6usize),
                    (1013usize, 384usize, 6usize),
                    (1014usize, 390usize, 6usize),
                    (1015usize, 396usize, 6usize),
                    (1016usize, 402usize, 6usize),
                    (1017usize, 408usize, 6usize),
                    (1018usize, 414usize, 6usize),
                    (1019usize, 420usize, 6usize),
                    (1020usize, 426usize, 6usize),
                    (1021usize, 432usize, 6usize),
                    (1022usize, 438usize, 6usize),
                    (1023usize, 444usize, 6usize),
                    (1024usize, 450usize, 6usize),
                    (1025usize, 456usize, 6usize),
                    (1026usize, 462usize, 6usize),
                    (1027usize, 468usize, 6usize),
                    (1028usize, 474usize, 6usize),
                    (1029usize, 480usize, 6usize),
                    (1030usize, 486usize, 6usize),
                    (1031usize, 492usize, 6usize),
                    (1032usize, 498usize, 6usize),
                    (1033usize, 504usize, 6usize),
                    (1034usize, 510usize, 6usize),
                    (1035usize, 516usize, 6usize),
                    (1036usize, 522usize, 6usize),
                    (1037usize, 528usize, 6usize),
                    (1038usize, 534usize, 6usize),
                    (1039usize, 540usize, 6usize),
                    (1040usize, 546usize, 6usize),
                    (1041usize, 552usize, 6usize),
                    (1042usize, 558usize, 6usize),
                    (1043usize, 564usize, 6usize),
                    (1044usize, 570usize, 6usize),
                    (1045usize, 576usize, 6usize),
                    (1046usize, 582usize, 6usize),
                    (1047usize, 588usize, 6usize),
                    (1048usize, 594usize, 6usize),
                    (1049usize, 600usize, 6usize),
                    (1050usize, 606usize, 6usize),
                    (1051usize, 612usize, 6usize),
                    (1052usize, 618usize, 6usize),
                    (1053usize, 624usize, 6usize),
                    (1054usize, 630usize, 6usize),
                    (1055usize, 636usize, 6usize),
                    (1056usize, 642usize, 6usize),
                    (1057usize, 648usize, 6usize),
                    (1058usize, 654usize, 6usize),
                    (1059usize, 660usize, 6usize),
                    (1060usize, 666usize, 6usize),
                    (1061usize, 672usize, 6usize),
                    (1062usize, 678usize, 6usize),
                    (1063usize, 684usize, 6usize),
                    (1064usize, 690usize, 6usize),
                    (1065usize, 696usize, 6usize),
                    (1066usize, 702usize, 6usize),
                    (1067usize, 708usize, 6usize),
                    (1068usize, 714usize, 6usize),
                    (1069usize, 720usize, 6usize),
                    (1070usize, 726usize, 6usize),
                    (1071usize, 732usize, 6usize),
                    (1072usize, 738usize, 6usize),
                    (1073usize, 744usize, 6usize),
                    (1074usize, 750usize, 6usize),
                    (1075usize, 756usize, 6usize),
                    (1076usize, 762usize, 6usize),
                    (1077usize, 768usize, 6usize),
                    (1078usize, 774usize, 6usize),
                    (1079usize, 780usize, 6usize),
                    (1080usize, 786usize, 6usize),
                    (1081usize, 792usize, 6usize),
                    (1082usize, 798usize, 6usize),
                    (1083usize, 804usize, 6usize),
                    (1084usize, 810usize, 6usize),
                    (1085usize, 816usize, 6usize),
                    (1086usize, 822usize, 6usize),
                    (1087usize, 828usize, 6usize),
                    (1088usize, 834usize, 6usize),
                    (1089usize, 840usize, 6usize),
                    (1090usize, 846usize, 6usize),
                    (1091usize, 852usize, 6usize),
                    (1092usize, 858usize, 6usize),
                    (1093usize, 864usize, 6usize),
                    (1094usize, 870usize, 6usize),
                    (1095usize, 876usize, 6usize),
                    (1096usize, 882usize, 6usize),
                    (1097usize, 888usize, 6usize),
                    (1098usize, 894usize, 6usize),
                    (1099usize, 900usize, 6usize),
                    (1100usize, 906usize, 6usize),
                    (1101usize, 912usize, 6usize),
                    (1102usize, 918usize, 6usize),
                    (1103usize, 924usize, 6usize),
                    (1104usize, 930usize, 6usize),
                    (1105usize, 936usize, 6usize),
                    (1106usize, 942usize, 6usize),
                    (1107usize, 948usize, 6usize),
                    (1108usize, 954usize, 6usize),
                    (1109usize, 960usize, 6usize),
                    (1110usize, 966usize, 6usize),
                    (1111usize, 972usize, 6usize),
                    (1112usize, 978usize, 6usize),
                    (1113usize, 984usize, 6usize),
                    (1114usize, 990usize, 6usize),
                    (1115usize, 996usize, 6usize),
                    (1116usize, 1002usize, 6usize),
                    (1117usize, 1008usize, 6usize),
                    (1118usize, 1014usize, 6usize),
                    (1119usize, 1020usize, 6usize),
                    (1120usize, 1026usize, 6usize),
                    (1121usize, 1032usize, 6usize),
                    (1122usize, 1038usize, 6usize),
                    (1123usize, 1044usize, 6usize),
                    (1124usize, 1050usize, 6usize),
                    (1125usize, 1056usize, 6usize),
                    (1126usize, 1062usize, 6usize),
                    (1127usize, 1068usize, 6usize),
                    (1128usize, 1074usize, 6usize),
                    (1129usize, 1080usize, 6usize),
                    (1130usize, 1086usize, 6usize),
                    (1131usize, 1092usize, 6usize),
                    (1132usize, 1098usize, 6usize),
                    (1133usize, 1104usize, 6usize),
                    (1134usize, 1110usize, 6usize),
                    (1135usize, 1116usize, 6usize),
                    (1136usize, 1122usize, 6usize),
                    (1137usize, 1128usize, 6usize),
                    (1138usize, 1134usize, 6usize),
                    (1139usize, 1140usize, 6usize),
                ];
                const VL_COLS: [(u32, usize, usize); 1146usize] = [
                    (0u32, 0usize, 1usize),
                    (0u32, 1usize, 1usize),
                    (0u32, 2usize, 1usize),
                    (0u32, 3usize, 1usize),
                    (0u32, 4usize, 0usize),
                    (1073741688u32, 4usize, 0usize),
                    (0u32, 4usize, 2usize),
                    (0u32, 6usize, 5usize),
                    (0u32, 11usize, 1usize),
                    (0u32, 12usize, 0usize),
                    (0u32, 12usize, 0usize),
                    (1073741816u32, 12usize, 0usize),
                    (0u32, 12usize, 1usize),
                    (0u32, 13usize, 1usize),
                    (0u32, 14usize, 1usize),
                    (0u32, 15usize, 1usize),
                    (0u32, 16usize, 0usize),
                    (1073741688u32, 16usize, 0usize),
                    (0u32, 16usize, 2usize),
                    (0u32, 18usize, 6usize),
                    (0u32, 24usize, 1usize),
                    (0u32, 25usize, 0usize),
                    (0u32, 25usize, 0usize),
                    (1073741816u32, 25usize, 0usize),
                    (0u32, 25usize, 1usize),
                    (0u32, 26usize, 1usize),
                    (0u32, 27usize, 1usize),
                    (0u32, 28usize, 0usize),
                    (0u32, 28usize, 0usize),
                    (1342177238u32, 28usize, 0usize),
                    (0u32, 28usize, 1usize),
                    (0u32, 29usize, 1usize),
                    (0u32, 30usize, 1usize),
                    (0u32, 31usize, 0usize),
                    (0u32, 31usize, 0usize),
                    (1342177238u32, 31usize, 0usize),
                    (0u32, 31usize, 3usize),
                    (0u32, 34usize, 1usize),
                    (0u32, 35usize, 6usize),
                    (0u32, 41usize, 1usize),
                    (0u32, 42usize, 1usize),
                    (1610612596u32, 43usize, 0usize),
                    (0u32, 43usize, 3usize),
                    (0u32, 46usize, 1usize),
                    (0u32, 47usize, 7usize),
                    (0u32, 54usize, 1usize),
                    (0u32, 55usize, 1usize),
                    (1610612596u32, 56usize, 0usize),
                    (0u32, 56usize, 1usize),
                    (0u32, 57usize, 9usize),
                    (0u32, 66usize, 1usize),
                    (0u32, 67usize, 0usize),
                    (0u32, 67usize, 0usize),
                    (1073741816u32, 67usize, 0usize),
                    (0u32, 67usize, 1usize),
                    (0u32, 68usize, 11usize),
                    (0u32, 79usize, 1usize),
                    (0u32, 80usize, 0usize),
                    (0u32, 80usize, 0usize),
                    (1073741816u32, 80usize, 0usize),
                    (0u32, 80usize, 1usize),
                    (0u32, 81usize, 1usize),
                    (0u32, 82usize, 1usize),
                    (0u32, 83usize, 1usize),
                    (0u32, 84usize, 0usize),
                    (1073741688u32, 84usize, 0usize),
                    (0u32, 84usize, 1usize),
                    (0u32, 85usize, 1usize),
                    (0u32, 86usize, 1usize),
                    (0u32, 87usize, 1usize),
                    (0u32, 88usize, 0usize),
                    (1073741688u32, 88usize, 0usize),
                    (0u32, 88usize, 1usize),
                    (0u32, 89usize, 8usize),
                    (0u32, 97usize, 1usize),
                    (0u32, 98usize, 0usize),
                    (0u32, 98usize, 0usize),
                    (1342177238u32, 98usize, 0usize),
                    (0u32, 98usize, 1usize),
                    (0u32, 99usize, 10usize),
                    (0u32, 109usize, 1usize),
                    (0u32, 110usize, 0usize),
                    (0u32, 110usize, 0usize),
                    (1342177238u32, 110usize, 0usize),
                    (0u32, 110usize, 1usize),
                    (0u32, 111usize, 1usize),
                    (0u32, 112usize, 1usize),
                    (0u32, 113usize, 0usize),
                    (0u32, 113usize, 0usize),
                    (1073741784u32, 113usize, 0usize),
                    (0u32, 113usize, 1usize),
                    (0u32, 114usize, 1usize),
                    (0u32, 115usize, 1usize),
                    (0u32, 116usize, 0usize),
                    (0u32, 116usize, 0usize),
                    (1073741784u32, 116usize, 0usize),
                    (0u32, 116usize, 1usize),
                    (0u32, 117usize, 1usize),
                    (0u32, 118usize, 1usize),
                    (0u32, 119usize, 1usize),
                    (0u32, 120usize, 0usize),
                    (1073741688u32, 120usize, 0usize),
                    (0u32, 120usize, 2usize),
                    (0u32, 122usize, 5usize),
                    (0u32, 127usize, 1usize),
                    (0u32, 128usize, 0usize),
                    (0u32, 128usize, 0usize),
                    (1073741816u32, 128usize, 0usize),
                    (0u32, 128usize, 1usize),
                    (0u32, 129usize, 1usize),
                    (0u32, 130usize, 1usize),
                    (0u32, 131usize, 1usize),
                    (0u32, 132usize, 0usize),
                    (1073741688u32, 132usize, 0usize),
                    (0u32, 132usize, 2usize),
                    (0u32, 134usize, 6usize),
                    (0u32, 140usize, 1usize),
                    (0u32, 141usize, 0usize),
                    (0u32, 141usize, 0usize),
                    (1073741816u32, 141usize, 0usize),
                    (0u32, 141usize, 1usize),
                    (0u32, 142usize, 1usize),
                    (0u32, 143usize, 1usize),
                    (0u32, 144usize, 0usize),
                    (0u32, 144usize, 0usize),
                    (1342177238u32, 144usize, 0usize),
                    (0u32, 144usize, 1usize),
                    (0u32, 145usize, 1usize),
                    (0u32, 146usize, 1usize),
                    (0u32, 147usize, 0usize),
                    (0u32, 147usize, 0usize),
                    (1342177238u32, 147usize, 0usize),
                    (0u32, 147usize, 3usize),
                    (0u32, 150usize, 1usize),
                    (0u32, 151usize, 6usize),
                    (0u32, 157usize, 1usize),
                    (0u32, 158usize, 1usize),
                    (1610612596u32, 159usize, 0usize),
                    (0u32, 159usize, 3usize),
                    (0u32, 162usize, 1usize),
                    (0u32, 163usize, 7usize),
                    (0u32, 170usize, 1usize),
                    (0u32, 171usize, 1usize),
                    (1610612596u32, 172usize, 0usize),
                    (0u32, 172usize, 1usize),
                    (0u32, 173usize, 9usize),
                    (0u32, 182usize, 1usize),
                    (0u32, 183usize, 0usize),
                    (0u32, 183usize, 0usize),
                    (1073741816u32, 183usize, 0usize),
                    (0u32, 183usize, 1usize),
                    (0u32, 184usize, 11usize),
                    (0u32, 195usize, 1usize),
                    (0u32, 196usize, 0usize),
                    (0u32, 196usize, 0usize),
                    (1073741816u32, 196usize, 0usize),
                    (0u32, 196usize, 1usize),
                    (0u32, 197usize, 1usize),
                    (0u32, 198usize, 1usize),
                    (0u32, 199usize, 1usize),
                    (0u32, 200usize, 0usize),
                    (1073741688u32, 200usize, 0usize),
                    (0u32, 200usize, 1usize),
                    (0u32, 201usize, 1usize),
                    (0u32, 202usize, 1usize),
                    (0u32, 203usize, 1usize),
                    (0u32, 204usize, 0usize),
                    (1073741688u32, 204usize, 0usize),
                    (0u32, 204usize, 1usize),
                    (0u32, 205usize, 8usize),
                    (0u32, 213usize, 1usize),
                    (0u32, 214usize, 0usize),
                    (0u32, 214usize, 0usize),
                    (1342177238u32, 214usize, 0usize),
                    (0u32, 214usize, 1usize),
                    (0u32, 215usize, 10usize),
                    (0u32, 225usize, 1usize),
                    (0u32, 226usize, 0usize),
                    (0u32, 226usize, 0usize),
                    (1342177238u32, 226usize, 0usize),
                    (0u32, 226usize, 1usize),
                    (0u32, 227usize, 1usize),
                    (0u32, 228usize, 1usize),
                    (0u32, 229usize, 0usize),
                    (0u32, 229usize, 0usize),
                    (1073741784u32, 229usize, 0usize),
                    (0u32, 229usize, 1usize),
                    (0u32, 230usize, 1usize),
                    (0u32, 231usize, 1usize),
                    (0u32, 232usize, 0usize),
                    (0u32, 232usize, 0usize),
                    (1073741784u32, 232usize, 0usize),
                    (0u32, 232usize, 1usize),
                    (0u32, 233usize, 1usize),
                    (0u32, 234usize, 1usize),
                    (0u32, 235usize, 1usize),
                    (0u32, 236usize, 0usize),
                    (1073741688u32, 236usize, 0usize),
                    (0u32, 236usize, 2usize),
                    (0u32, 238usize, 5usize),
                    (0u32, 243usize, 1usize),
                    (0u32, 244usize, 0usize),
                    (0u32, 244usize, 0usize),
                    (1073741816u32, 244usize, 0usize),
                    (0u32, 244usize, 1usize),
                    (0u32, 245usize, 1usize),
                    (0u32, 246usize, 1usize),
                    (0u32, 247usize, 1usize),
                    (0u32, 248usize, 0usize),
                    (1073741688u32, 248usize, 0usize),
                    (0u32, 248usize, 2usize),
                    (0u32, 250usize, 6usize),
                    (0u32, 256usize, 1usize),
                    (0u32, 257usize, 0usize),
                    (0u32, 257usize, 0usize),
                    (1073741816u32, 257usize, 0usize),
                    (0u32, 257usize, 1usize),
                    (0u32, 258usize, 1usize),
                    (0u32, 259usize, 1usize),
                    (0u32, 260usize, 0usize),
                    (0u32, 260usize, 0usize),
                    (1342177238u32, 260usize, 0usize),
                    (0u32, 260usize, 1usize),
                    (0u32, 261usize, 1usize),
                    (0u32, 262usize, 1usize),
                    (0u32, 263usize, 0usize),
                    (0u32, 263usize, 0usize),
                    (1342177238u32, 263usize, 0usize),
                    (0u32, 263usize, 3usize),
                    (0u32, 266usize, 1usize),
                    (0u32, 267usize, 6usize),
                    (0u32, 273usize, 1usize),
                    (0u32, 274usize, 1usize),
                    (1610612596u32, 275usize, 0usize),
                    (0u32, 275usize, 3usize),
                    (0u32, 278usize, 1usize),
                    (0u32, 279usize, 7usize),
                    (0u32, 286usize, 1usize),
                    (0u32, 287usize, 1usize),
                    (1610612596u32, 288usize, 0usize),
                    (0u32, 288usize, 1usize),
                    (0u32, 289usize, 9usize),
                    (0u32, 298usize, 1usize),
                    (0u32, 299usize, 0usize),
                    (0u32, 299usize, 0usize),
                    (1073741816u32, 299usize, 0usize),
                    (0u32, 299usize, 1usize),
                    (0u32, 300usize, 11usize),
                    (0u32, 311usize, 1usize),
                    (0u32, 312usize, 0usize),
                    (0u32, 312usize, 0usize),
                    (1073741816u32, 312usize, 0usize),
                    (0u32, 312usize, 1usize),
                    (0u32, 313usize, 1usize),
                    (0u32, 314usize, 1usize),
                    (0u32, 315usize, 1usize),
                    (0u32, 316usize, 0usize),
                    (1073741688u32, 316usize, 0usize),
                    (0u32, 316usize, 1usize),
                    (0u32, 317usize, 1usize),
                    (0u32, 318usize, 1usize),
                    (0u32, 319usize, 1usize),
                    (0u32, 320usize, 0usize),
                    (1073741688u32, 320usize, 0usize),
                    (0u32, 320usize, 1usize),
                    (0u32, 321usize, 8usize),
                    (0u32, 329usize, 1usize),
                    (0u32, 330usize, 0usize),
                    (0u32, 330usize, 0usize),
                    (1342177238u32, 330usize, 0usize),
                    (0u32, 330usize, 1usize),
                    (0u32, 331usize, 10usize),
                    (0u32, 341usize, 1usize),
                    (0u32, 342usize, 0usize),
                    (0u32, 342usize, 0usize),
                    (1342177238u32, 342usize, 0usize),
                    (0u32, 342usize, 1usize),
                    (0u32, 343usize, 1usize),
                    (0u32, 344usize, 1usize),
                    (0u32, 345usize, 0usize),
                    (0u32, 345usize, 0usize),
                    (1073741784u32, 345usize, 0usize),
                    (0u32, 345usize, 1usize),
                    (0u32, 346usize, 1usize),
                    (0u32, 347usize, 1usize),
                    (0u32, 348usize, 0usize),
                    (0u32, 348usize, 0usize),
                    (1073741784u32, 348usize, 0usize),
                    (0u32, 348usize, 1usize),
                    (0u32, 349usize, 1usize),
                    (0u32, 350usize, 1usize),
                    (0u32, 351usize, 1usize),
                    (0u32, 352usize, 0usize),
                    (1073741688u32, 352usize, 0usize),
                    (0u32, 352usize, 2usize),
                    (0u32, 354usize, 5usize),
                    (0u32, 359usize, 1usize),
                    (0u32, 360usize, 0usize),
                    (0u32, 360usize, 0usize),
                    (1073741816u32, 360usize, 0usize),
                    (0u32, 360usize, 1usize),
                    (0u32, 361usize, 1usize),
                    (0u32, 362usize, 1usize),
                    (0u32, 363usize, 1usize),
                    (0u32, 364usize, 0usize),
                    (1073741688u32, 364usize, 0usize),
                    (0u32, 364usize, 2usize),
                    (0u32, 366usize, 6usize),
                    (0u32, 372usize, 1usize),
                    (0u32, 373usize, 0usize),
                    (0u32, 373usize, 0usize),
                    (1073741816u32, 373usize, 0usize),
                    (0u32, 373usize, 1usize),
                    (0u32, 374usize, 1usize),
                    (0u32, 375usize, 1usize),
                    (0u32, 376usize, 0usize),
                    (0u32, 376usize, 0usize),
                    (1342177238u32, 376usize, 0usize),
                    (0u32, 376usize, 1usize),
                    (0u32, 377usize, 1usize),
                    (0u32, 378usize, 1usize),
                    (0u32, 379usize, 0usize),
                    (0u32, 379usize, 0usize),
                    (1342177238u32, 379usize, 0usize),
                    (0u32, 379usize, 3usize),
                    (0u32, 382usize, 1usize),
                    (0u32, 383usize, 6usize),
                    (0u32, 389usize, 1usize),
                    (0u32, 390usize, 1usize),
                    (1610612596u32, 391usize, 0usize),
                    (0u32, 391usize, 3usize),
                    (0u32, 394usize, 1usize),
                    (0u32, 395usize, 7usize),
                    (0u32, 402usize, 1usize),
                    (0u32, 403usize, 1usize),
                    (1610612596u32, 404usize, 0usize),
                    (0u32, 404usize, 1usize),
                    (0u32, 405usize, 9usize),
                    (0u32, 414usize, 1usize),
                    (0u32, 415usize, 0usize),
                    (0u32, 415usize, 0usize),
                    (1073741816u32, 415usize, 0usize),
                    (0u32, 415usize, 1usize),
                    (0u32, 416usize, 11usize),
                    (0u32, 427usize, 1usize),
                    (0u32, 428usize, 0usize),
                    (0u32, 428usize, 0usize),
                    (1073741816u32, 428usize, 0usize),
                    (0u32, 428usize, 1usize),
                    (0u32, 429usize, 1usize),
                    (0u32, 430usize, 1usize),
                    (0u32, 431usize, 1usize),
                    (0u32, 432usize, 0usize),
                    (1073741688u32, 432usize, 0usize),
                    (0u32, 432usize, 1usize),
                    (0u32, 433usize, 1usize),
                    (0u32, 434usize, 1usize),
                    (0u32, 435usize, 1usize),
                    (0u32, 436usize, 0usize),
                    (1073741688u32, 436usize, 0usize),
                    (0u32, 436usize, 1usize),
                    (0u32, 437usize, 8usize),
                    (0u32, 445usize, 1usize),
                    (0u32, 446usize, 0usize),
                    (0u32, 446usize, 0usize),
                    (1342177238u32, 446usize, 0usize),
                    (0u32, 446usize, 1usize),
                    (0u32, 447usize, 10usize),
                    (0u32, 457usize, 1usize),
                    (0u32, 458usize, 0usize),
                    (0u32, 458usize, 0usize),
                    (1342177238u32, 458usize, 0usize),
                    (0u32, 458usize, 1usize),
                    (0u32, 459usize, 1usize),
                    (0u32, 460usize, 1usize),
                    (0u32, 461usize, 0usize),
                    (0u32, 461usize, 0usize),
                    (1073741784u32, 461usize, 0usize),
                    (0u32, 461usize, 1usize),
                    (0u32, 462usize, 1usize),
                    (0u32, 463usize, 1usize),
                    (0u32, 464usize, 0usize),
                    (0u32, 464usize, 0usize),
                    (1073741784u32, 464usize, 0usize),
                    (0u32, 464usize, 1usize),
                    (0u32, 465usize, 1usize),
                    (0u32, 466usize, 1usize),
                    (0u32, 467usize, 1usize),
                    (0u32, 468usize, 0usize),
                    (1073741688u32, 468usize, 0usize),
                    (0u32, 468usize, 1usize),
                    (0u32, 469usize, 13usize),
                    (0u32, 482usize, 1usize),
                    (0u32, 483usize, 0usize),
                    (0u32, 483usize, 0usize),
                    (1073741816u32, 483usize, 0usize),
                    (0u32, 483usize, 1usize),
                    (0u32, 484usize, 1usize),
                    (0u32, 485usize, 1usize),
                    (0u32, 486usize, 1usize),
                    (0u32, 487usize, 0usize),
                    (1073741688u32, 487usize, 0usize),
                    (0u32, 487usize, 1usize),
                    (0u32, 488usize, 16usize),
                    (0u32, 504usize, 1usize),
                    (0u32, 505usize, 0usize),
                    (0u32, 505usize, 0usize),
                    (1073741816u32, 505usize, 0usize),
                    (0u32, 505usize, 1usize),
                    (0u32, 506usize, 1usize),
                    (0u32, 507usize, 1usize),
                    (0u32, 508usize, 0usize),
                    (0u32, 508usize, 0usize),
                    (1342177238u32, 508usize, 0usize),
                    (0u32, 508usize, 1usize),
                    (0u32, 509usize, 1usize),
                    (0u32, 510usize, 1usize),
                    (0u32, 511usize, 0usize),
                    (0u32, 511usize, 0usize),
                    (1342177238u32, 511usize, 0usize),
                    (0u32, 511usize, 4usize),
                    (0u32, 515usize, 1usize),
                    (0u32, 516usize, 12usize),
                    (0u32, 528usize, 1usize),
                    (0u32, 529usize, 1usize),
                    (1610612596u32, 530usize, 0usize),
                    (0u32, 530usize, 4usize),
                    (0u32, 534usize, 1usize),
                    (0u32, 535usize, 15usize),
                    (0u32, 550usize, 1usize),
                    (0u32, 551usize, 1usize),
                    (1610612596u32, 552usize, 0usize),
                    (0u32, 552usize, 1usize),
                    (0u32, 553usize, 2usize),
                    (0u32, 555usize, 1usize),
                    (0u32, 556usize, 0usize),
                    (0u32, 556usize, 0usize),
                    (1073741816u32, 556usize, 0usize),
                    (0u32, 556usize, 1usize),
                    (0u32, 557usize, 2usize),
                    (0u32, 559usize, 1usize),
                    (0u32, 560usize, 0usize),
                    (0u32, 560usize, 0usize),
                    (1073741816u32, 560usize, 0usize),
                    (0u32, 560usize, 1usize),
                    (0u32, 561usize, 1usize),
                    (0u32, 562usize, 16usize),
                    (0u32, 578usize, 2usize),
                    (0u32, 580usize, 0usize),
                    (1073741688u32, 580usize, 0usize),
                    (0u32, 580usize, 1usize),
                    (0u32, 581usize, 1usize),
                    (0u32, 582usize, 29usize),
                    (0u32, 611usize, 2usize),
                    (0u32, 613usize, 0usize),
                    (1073741688u32, 613usize, 0usize),
                    (0u32, 613usize, 1usize),
                    (0u32, 614usize, 2usize),
                    (0u32, 616usize, 1usize),
                    (0u32, 617usize, 0usize),
                    (0u32, 617usize, 0usize),
                    (1342177238u32, 617usize, 0usize),
                    (0u32, 617usize, 1usize),
                    (0u32, 618usize, 2usize),
                    (0u32, 620usize, 1usize),
                    (0u32, 621usize, 0usize),
                    (0u32, 621usize, 0usize),
                    (1342177238u32, 621usize, 0usize),
                    (0u32, 621usize, 1usize),
                    (0u32, 622usize, 1usize),
                    (0u32, 623usize, 12usize),
                    (0u32, 635usize, 2usize),
                    (0u32, 637usize, 0usize),
                    (1342177142u32, 637usize, 0usize),
                    (0u32, 637usize, 1usize),
                    (0u32, 638usize, 1usize),
                    (0u32, 639usize, 21usize),
                    (0u32, 660usize, 2usize),
                    (0u32, 662usize, 0usize),
                    (1342177142u32, 662usize, 0usize),
                    (0u32, 662usize, 1usize),
                    (0u32, 663usize, 1usize),
                    (0u32, 664usize, 1usize),
                    (0u32, 665usize, 1usize),
                    (0u32, 666usize, 0usize),
                    (1073741688u32, 666usize, 0usize),
                    (0u32, 666usize, 1usize),
                    (0u32, 667usize, 13usize),
                    (0u32, 680usize, 1usize),
                    (0u32, 681usize, 0usize),
                    (0u32, 681usize, 0usize),
                    (1073741816u32, 681usize, 0usize),
                    (0u32, 681usize, 1usize),
                    (0u32, 682usize, 1usize),
                    (0u32, 683usize, 1usize),
                    (0u32, 684usize, 1usize),
                    (0u32, 685usize, 0usize),
                    (1073741688u32, 685usize, 0usize),
                    (0u32, 685usize, 1usize),
                    (0u32, 686usize, 16usize),
                    (0u32, 702usize, 1usize),
                    (0u32, 703usize, 0usize),
                    (0u32, 703usize, 0usize),
                    (1073741816u32, 703usize, 0usize),
                    (0u32, 703usize, 1usize),
                    (0u32, 704usize, 1usize),
                    (0u32, 705usize, 1usize),
                    (0u32, 706usize, 0usize),
                    (0u32, 706usize, 0usize),
                    (1342177238u32, 706usize, 0usize),
                    (0u32, 706usize, 1usize),
                    (0u32, 707usize, 1usize),
                    (0u32, 708usize, 1usize),
                    (0u32, 709usize, 0usize),
                    (0u32, 709usize, 0usize),
                    (1342177238u32, 709usize, 0usize),
                    (0u32, 709usize, 4usize),
                    (0u32, 713usize, 1usize),
                    (0u32, 714usize, 12usize),
                    (0u32, 726usize, 1usize),
                    (0u32, 727usize, 1usize),
                    (1610612596u32, 728usize, 0usize),
                    (0u32, 728usize, 4usize),
                    (0u32, 732usize, 1usize),
                    (0u32, 733usize, 15usize),
                    (0u32, 748usize, 1usize),
                    (0u32, 749usize, 1usize),
                    (1610612596u32, 750usize, 0usize),
                    (0u32, 750usize, 1usize),
                    (0u32, 751usize, 2usize),
                    (0u32, 753usize, 1usize),
                    (0u32, 754usize, 0usize),
                    (0u32, 754usize, 0usize),
                    (1073741816u32, 754usize, 0usize),
                    (0u32, 754usize, 1usize),
                    (0u32, 755usize, 2usize),
                    (0u32, 757usize, 1usize),
                    (0u32, 758usize, 0usize),
                    (0u32, 758usize, 0usize),
                    (1073741816u32, 758usize, 0usize),
                    (0u32, 758usize, 1usize),
                    (0u32, 759usize, 1usize),
                    (0u32, 760usize, 16usize),
                    (0u32, 776usize, 2usize),
                    (0u32, 778usize, 0usize),
                    (1073741688u32, 778usize, 0usize),
                    (0u32, 778usize, 1usize),
                    (0u32, 779usize, 1usize),
                    (0u32, 780usize, 29usize),
                    (0u32, 809usize, 2usize),
                    (0u32, 811usize, 0usize),
                    (1073741688u32, 811usize, 0usize),
                    (0u32, 811usize, 1usize),
                    (0u32, 812usize, 2usize),
                    (0u32, 814usize, 1usize),
                    (0u32, 815usize, 0usize),
                    (0u32, 815usize, 0usize),
                    (1342177238u32, 815usize, 0usize),
                    (0u32, 815usize, 1usize),
                    (0u32, 816usize, 2usize),
                    (0u32, 818usize, 1usize),
                    (0u32, 819usize, 0usize),
                    (0u32, 819usize, 0usize),
                    (1342177238u32, 819usize, 0usize),
                    (0u32, 819usize, 1usize),
                    (0u32, 820usize, 1usize),
                    (0u32, 821usize, 12usize),
                    (0u32, 833usize, 2usize),
                    (0u32, 835usize, 0usize),
                    (1342177142u32, 835usize, 0usize),
                    (0u32, 835usize, 1usize),
                    (0u32, 836usize, 1usize),
                    (0u32, 837usize, 21usize),
                    (0u32, 858usize, 2usize),
                    (0u32, 860usize, 0usize),
                    (1342177142u32, 860usize, 0usize),
                    (0u32, 860usize, 1usize),
                    (0u32, 861usize, 1usize),
                    (0u32, 862usize, 1usize),
                    (0u32, 863usize, 1usize),
                    (0u32, 864usize, 0usize),
                    (1073741688u32, 864usize, 0usize),
                    (0u32, 864usize, 1usize),
                    (0u32, 865usize, 13usize),
                    (0u32, 878usize, 1usize),
                    (0u32, 879usize, 0usize),
                    (0u32, 879usize, 0usize),
                    (1073741816u32, 879usize, 0usize),
                    (0u32, 879usize, 1usize),
                    (0u32, 880usize, 1usize),
                    (0u32, 881usize, 1usize),
                    (0u32, 882usize, 1usize),
                    (0u32, 883usize, 0usize),
                    (1073741688u32, 883usize, 0usize),
                    (0u32, 883usize, 1usize),
                    (0u32, 884usize, 16usize),
                    (0u32, 900usize, 1usize),
                    (0u32, 901usize, 0usize),
                    (0u32, 901usize, 0usize),
                    (1073741816u32, 901usize, 0usize),
                    (0u32, 901usize, 1usize),
                    (0u32, 902usize, 1usize),
                    (0u32, 903usize, 1usize),
                    (0u32, 904usize, 0usize),
                    (0u32, 904usize, 0usize),
                    (1342177238u32, 904usize, 0usize),
                    (0u32, 904usize, 1usize),
                    (0u32, 905usize, 1usize),
                    (0u32, 906usize, 1usize),
                    (0u32, 907usize, 0usize),
                    (0u32, 907usize, 0usize),
                    (1342177238u32, 907usize, 0usize),
                    (0u32, 907usize, 4usize),
                    (0u32, 911usize, 1usize),
                    (0u32, 912usize, 12usize),
                    (0u32, 924usize, 1usize),
                    (0u32, 925usize, 1usize),
                    (1610612596u32, 926usize, 0usize),
                    (0u32, 926usize, 4usize),
                    (0u32, 930usize, 1usize),
                    (0u32, 931usize, 15usize),
                    (0u32, 946usize, 1usize),
                    (0u32, 947usize, 1usize),
                    (1610612596u32, 948usize, 0usize),
                    (0u32, 948usize, 1usize),
                    (0u32, 949usize, 2usize),
                    (0u32, 951usize, 1usize),
                    (0u32, 952usize, 0usize),
                    (0u32, 952usize, 0usize),
                    (1073741816u32, 952usize, 0usize),
                    (0u32, 952usize, 1usize),
                    (0u32, 953usize, 2usize),
                    (0u32, 955usize, 1usize),
                    (0u32, 956usize, 0usize),
                    (0u32, 956usize, 0usize),
                    (1073741816u32, 956usize, 0usize),
                    (0u32, 956usize, 1usize),
                    (0u32, 957usize, 1usize),
                    (0u32, 958usize, 16usize),
                    (0u32, 974usize, 2usize),
                    (0u32, 976usize, 0usize),
                    (1073741688u32, 976usize, 0usize),
                    (0u32, 976usize, 1usize),
                    (0u32, 977usize, 1usize),
                    (0u32, 978usize, 29usize),
                    (0u32, 1007usize, 2usize),
                    (0u32, 1009usize, 0usize),
                    (1073741688u32, 1009usize, 0usize),
                    (0u32, 1009usize, 1usize),
                    (0u32, 1010usize, 2usize),
                    (0u32, 1012usize, 1usize),
                    (0u32, 1013usize, 0usize),
                    (0u32, 1013usize, 0usize),
                    (1342177238u32, 1013usize, 0usize),
                    (0u32, 1013usize, 1usize),
                    (0u32, 1014usize, 2usize),
                    (0u32, 1016usize, 1usize),
                    (0u32, 1017usize, 0usize),
                    (0u32, 1017usize, 0usize),
                    (1342177238u32, 1017usize, 0usize),
                    (0u32, 1017usize, 1usize),
                    (0u32, 1018usize, 1usize),
                    (0u32, 1019usize, 12usize),
                    (0u32, 1031usize, 2usize),
                    (0u32, 1033usize, 0usize),
                    (1342177142u32, 1033usize, 0usize),
                    (0u32, 1033usize, 1usize),
                    (0u32, 1034usize, 1usize),
                    (0u32, 1035usize, 21usize),
                    (0u32, 1056usize, 2usize),
                    (0u32, 1058usize, 0usize),
                    (1342177142u32, 1058usize, 0usize),
                    (0u32, 1058usize, 1usize),
                    (0u32, 1059usize, 1usize),
                    (0u32, 1060usize, 1usize),
                    (0u32, 1061usize, 1usize),
                    (0u32, 1062usize, 0usize),
                    (1073741688u32, 1062usize, 0usize),
                    (0u32, 1062usize, 1usize),
                    (0u32, 1063usize, 13usize),
                    (0u32, 1076usize, 1usize),
                    (0u32, 1077usize, 0usize),
                    (0u32, 1077usize, 0usize),
                    (1073741816u32, 1077usize, 0usize),
                    (0u32, 1077usize, 1usize),
                    (0u32, 1078usize, 1usize),
                    (0u32, 1079usize, 1usize),
                    (0u32, 1080usize, 1usize),
                    (0u32, 1081usize, 0usize),
                    (1073741688u32, 1081usize, 0usize),
                    (0u32, 1081usize, 1usize),
                    (0u32, 1082usize, 16usize),
                    (0u32, 1098usize, 1usize),
                    (0u32, 1099usize, 0usize),
                    (0u32, 1099usize, 0usize),
                    (1073741816u32, 1099usize, 0usize),
                    (0u32, 1099usize, 1usize),
                    (0u32, 1100usize, 1usize),
                    (0u32, 1101usize, 1usize),
                    (0u32, 1102usize, 0usize),
                    (0u32, 1102usize, 0usize),
                    (1342177238u32, 1102usize, 0usize),
                    (0u32, 1102usize, 1usize),
                    (0u32, 1103usize, 1usize),
                    (0u32, 1104usize, 1usize),
                    (0u32, 1105usize, 0usize),
                    (0u32, 1105usize, 0usize),
                    (1342177238u32, 1105usize, 0usize),
                    (0u32, 1105usize, 4usize),
                    (0u32, 1109usize, 1usize),
                    (0u32, 1110usize, 12usize),
                    (0u32, 1122usize, 1usize),
                    (0u32, 1123usize, 1usize),
                    (1610612596u32, 1124usize, 0usize),
                    (0u32, 1124usize, 4usize),
                    (0u32, 1128usize, 1usize),
                    (0u32, 1129usize, 15usize),
                    (0u32, 1144usize, 1usize),
                    (0u32, 1145usize, 1usize),
                    (1610612596u32, 1146usize, 0usize),
                    (0u32, 1146usize, 1usize),
                    (0u32, 1147usize, 2usize),
                    (0u32, 1149usize, 1usize),
                    (0u32, 1150usize, 0usize),
                    (0u32, 1150usize, 0usize),
                    (1073741816u32, 1150usize, 0usize),
                    (0u32, 1150usize, 1usize),
                    (0u32, 1151usize, 2usize),
                    (0u32, 1153usize, 1usize),
                    (0u32, 1154usize, 0usize),
                    (0u32, 1154usize, 0usize),
                    (1073741816u32, 1154usize, 0usize),
                    (0u32, 1154usize, 1usize),
                    (0u32, 1155usize, 1usize),
                    (0u32, 1156usize, 16usize),
                    (0u32, 1172usize, 2usize),
                    (0u32, 1174usize, 0usize),
                    (1073741688u32, 1174usize, 0usize),
                    (0u32, 1174usize, 1usize),
                    (0u32, 1175usize, 1usize),
                    (0u32, 1176usize, 29usize),
                    (0u32, 1205usize, 2usize),
                    (0u32, 1207usize, 0usize),
                    (1073741688u32, 1207usize, 0usize),
                    (0u32, 1207usize, 1usize),
                    (0u32, 1208usize, 2usize),
                    (0u32, 1210usize, 1usize),
                    (0u32, 1211usize, 0usize),
                    (0u32, 1211usize, 0usize),
                    (1342177238u32, 1211usize, 0usize),
                    (0u32, 1211usize, 1usize),
                    (0u32, 1212usize, 2usize),
                    (0u32, 1214usize, 1usize),
                    (0u32, 1215usize, 0usize),
                    (0u32, 1215usize, 0usize),
                    (1342177238u32, 1215usize, 0usize),
                    (0u32, 1215usize, 1usize),
                    (0u32, 1216usize, 1usize),
                    (0u32, 1217usize, 12usize),
                    (0u32, 1229usize, 2usize),
                    (0u32, 1231usize, 0usize),
                    (1342177142u32, 1231usize, 0usize),
                    (0u32, 1231usize, 1usize),
                    (0u32, 1232usize, 1usize),
                    (0u32, 1233usize, 21usize),
                    (0u32, 1254usize, 2usize),
                    (0u32, 1256usize, 0usize),
                    (1342177142u32, 1256usize, 0usize),
                    (0u32, 1256usize, 1usize),
                    (0u32, 1257usize, 1usize),
                    (0u32, 1258usize, 1usize),
                    (0u32, 1259usize, 0usize),
                    (0u32, 1259usize, 0usize),
                    (1073741784u32, 1259usize, 0usize),
                    (0u32, 1259usize, 2usize),
                    (0u32, 1261usize, 2usize),
                    (0u32, 1263usize, 1usize),
                    (0u32, 1264usize, 0usize),
                    (0u32, 1264usize, 0usize),
                    (1342177238u32, 1264usize, 0usize),
                    (0u32, 1264usize, 1usize),
                    (0u32, 1265usize, 2usize),
                    (0u32, 1267usize, 1usize),
                    (0u32, 1268usize, 0usize),
                    (0u32, 1268usize, 0usize),
                    (1073741784u32, 1268usize, 0usize),
                    (0u32, 1268usize, 1usize),
                    (0u32, 1269usize, 3usize),
                    (0u32, 1272usize, 1usize),
                    (0u32, 1273usize, 0usize),
                    (0u32, 1273usize, 0usize),
                    (1342177238u32, 1273usize, 0usize),
                    (0u32, 1273usize, 1usize),
                    (0u32, 1274usize, 1usize),
                    (0u32, 1275usize, 1usize),
                    (0u32, 1276usize, 0usize),
                    (0u32, 1276usize, 0usize),
                    (1073741784u32, 1276usize, 0usize),
                    (0u32, 1276usize, 2usize),
                    (0u32, 1278usize, 2usize),
                    (0u32, 1280usize, 1usize),
                    (0u32, 1281usize, 0usize),
                    (0u32, 1281usize, 0usize),
                    (1342177238u32, 1281usize, 0usize),
                    (0u32, 1281usize, 1usize),
                    (0u32, 1282usize, 2usize),
                    (0u32, 1284usize, 1usize),
                    (0u32, 1285usize, 0usize),
                    (0u32, 1285usize, 0usize),
                    (1073741784u32, 1285usize, 0usize),
                    (0u32, 1285usize, 1usize),
                    (0u32, 1286usize, 3usize),
                    (0u32, 1289usize, 1usize),
                    (0u32, 1290usize, 0usize),
                    (0u32, 1290usize, 0usize),
                    (1342177238u32, 1290usize, 0usize),
                    (0u32, 1290usize, 1usize),
                    (0u32, 1291usize, 1usize),
                    (0u32, 1292usize, 1usize),
                    (0u32, 1293usize, 0usize),
                    (0u32, 1293usize, 0usize),
                    (1073741784u32, 1293usize, 0usize),
                    (0u32, 1293usize, 2usize),
                    (0u32, 1295usize, 2usize),
                    (0u32, 1297usize, 1usize),
                    (0u32, 1298usize, 0usize),
                    (0u32, 1298usize, 0usize),
                    (1342177238u32, 1298usize, 0usize),
                    (0u32, 1298usize, 1usize),
                    (0u32, 1299usize, 2usize),
                    (0u32, 1301usize, 1usize),
                    (0u32, 1302usize, 0usize),
                    (0u32, 1302usize, 0usize),
                    (1073741784u32, 1302usize, 0usize),
                    (0u32, 1302usize, 1usize),
                    (0u32, 1303usize, 3usize),
                    (0u32, 1306usize, 1usize),
                    (0u32, 1307usize, 0usize),
                    (0u32, 1307usize, 0usize),
                    (1342177238u32, 1307usize, 0usize),
                    (0u32, 1307usize, 1usize),
                    (0u32, 1308usize, 1usize),
                    (0u32, 1309usize, 1usize),
                    (0u32, 1310usize, 0usize),
                    (0u32, 1310usize, 0usize),
                    (1073741784u32, 1310usize, 0usize),
                    (0u32, 1310usize, 2usize),
                    (0u32, 1312usize, 2usize),
                    (0u32, 1314usize, 1usize),
                    (0u32, 1315usize, 0usize),
                    (0u32, 1315usize, 0usize),
                    (1342177238u32, 1315usize, 0usize),
                    (0u32, 1315usize, 1usize),
                    (0u32, 1316usize, 2usize),
                    (0u32, 1318usize, 1usize),
                    (0u32, 1319usize, 0usize),
                    (0u32, 1319usize, 0usize),
                    (1073741784u32, 1319usize, 0usize),
                    (0u32, 1319usize, 1usize),
                    (0u32, 1320usize, 3usize),
                    (0u32, 1323usize, 1usize),
                    (0u32, 1324usize, 0usize),
                    (0u32, 1324usize, 0usize),
                    (1342177238u32, 1324usize, 0usize),
                    (0u32, 1324usize, 1usize),
                    (0u32, 1325usize, 1usize),
                    (0u32, 1326usize, 1usize),
                    (0u32, 1327usize, 0usize),
                    (0u32, 1327usize, 0usize),
                    (1073741784u32, 1327usize, 0usize),
                    (0u32, 1327usize, 2usize),
                    (0u32, 1329usize, 2usize),
                    (0u32, 1331usize, 1usize),
                    (0u32, 1332usize, 0usize),
                    (0u32, 1332usize, 0usize),
                    (1342177238u32, 1332usize, 0usize),
                    (0u32, 1332usize, 1usize),
                    (0u32, 1333usize, 2usize),
                    (0u32, 1335usize, 1usize),
                    (0u32, 1336usize, 0usize),
                    (0u32, 1336usize, 0usize),
                    (1073741784u32, 1336usize, 0usize),
                    (0u32, 1336usize, 1usize),
                    (0u32, 1337usize, 3usize),
                    (0u32, 1340usize, 1usize),
                    (0u32, 1341usize, 0usize),
                    (0u32, 1341usize, 0usize),
                    (1342177238u32, 1341usize, 0usize),
                    (0u32, 1341usize, 1usize),
                    (0u32, 1342usize, 1usize),
                    (0u32, 1343usize, 1usize),
                    (0u32, 1344usize, 0usize),
                    (0u32, 1344usize, 0usize),
                    (1073741784u32, 1344usize, 0usize),
                    (0u32, 1344usize, 2usize),
                    (0u32, 1346usize, 2usize),
                    (0u32, 1348usize, 1usize),
                    (0u32, 1349usize, 0usize),
                    (0u32, 1349usize, 0usize),
                    (1342177238u32, 1349usize, 0usize),
                    (0u32, 1349usize, 1usize),
                    (0u32, 1350usize, 2usize),
                    (0u32, 1352usize, 1usize),
                    (0u32, 1353usize, 0usize),
                    (0u32, 1353usize, 0usize),
                    (1073741784u32, 1353usize, 0usize),
                    (0u32, 1353usize, 1usize),
                    (0u32, 1354usize, 3usize),
                    (0u32, 1357usize, 1usize),
                    (0u32, 1358usize, 0usize),
                    (0u32, 1358usize, 0usize),
                    (1342177238u32, 1358usize, 0usize),
                    (0u32, 1358usize, 1usize),
                    (0u32, 1359usize, 1usize),
                    (0u32, 1360usize, 1usize),
                    (0u32, 1361usize, 0usize),
                    (0u32, 1361usize, 0usize),
                    (1073741784u32, 1361usize, 0usize),
                    (0u32, 1361usize, 2usize),
                    (0u32, 1363usize, 2usize),
                    (0u32, 1365usize, 1usize),
                    (0u32, 1366usize, 0usize),
                    (0u32, 1366usize, 0usize),
                    (1342177238u32, 1366usize, 0usize),
                    (0u32, 1366usize, 1usize),
                    (0u32, 1367usize, 2usize),
                    (0u32, 1369usize, 1usize),
                    (0u32, 1370usize, 0usize),
                    (0u32, 1370usize, 0usize),
                    (1073741784u32, 1370usize, 0usize),
                    (0u32, 1370usize, 1usize),
                    (0u32, 1371usize, 3usize),
                    (0u32, 1374usize, 1usize),
                    (0u32, 1375usize, 0usize),
                    (0u32, 1375usize, 0usize),
                    (1342177238u32, 1375usize, 0usize),
                    (0u32, 1375usize, 1usize),
                    (0u32, 1376usize, 1usize),
                    (0u32, 1377usize, 1usize),
                    (0u32, 1378usize, 0usize),
                    (0u32, 1378usize, 0usize),
                    (1073741784u32, 1378usize, 0usize),
                    (0u32, 1378usize, 2usize),
                    (0u32, 1380usize, 2usize),
                    (0u32, 1382usize, 1usize),
                    (0u32, 1383usize, 0usize),
                    (0u32, 1383usize, 0usize),
                    (1342177238u32, 1383usize, 0usize),
                    (0u32, 1383usize, 1usize),
                    (0u32, 1384usize, 2usize),
                    (0u32, 1386usize, 1usize),
                    (0u32, 1387usize, 0usize),
                    (0u32, 1387usize, 0usize),
                    (1073741784u32, 1387usize, 0usize),
                    (0u32, 1387usize, 1usize),
                    (0u32, 1388usize, 3usize),
                    (0u32, 1391usize, 1usize),
                    (0u32, 1392usize, 0usize),
                    (0u32, 1392usize, 0usize),
                    (1342177238u32, 1392usize, 0usize),
                    (0u32, 1392usize, 1usize),
                    (0u32, 1393usize, 1usize),
                    (0u32, 1394usize, 1usize),
                    (0u32, 1395usize, 0usize),
                    (0u32, 1395usize, 0usize),
                    (1342177238u32, 1395usize, 0usize),
                    (0u32, 1395usize, 2usize),
                    (0u32, 1397usize, 2usize),
                    (0u32, 1399usize, 1usize),
                    (0u32, 1400usize, 0usize),
                    (0u32, 1400usize, 0usize),
                    (1073741784u32, 1400usize, 0usize),
                    (0u32, 1400usize, 1usize),
                    (0u32, 1401usize, 2usize),
                    (0u32, 1403usize, 1usize),
                    (0u32, 1404usize, 0usize),
                    (0u32, 1404usize, 0usize),
                    (1073741816u32, 1404usize, 0usize),
                    (0u32, 1404usize, 2usize),
                    (0u32, 1406usize, 2usize),
                    (0u32, 1408usize, 1usize),
                    (0u32, 1409usize, 0usize),
                    (0u32, 1409usize, 0usize),
                    (1073741816u32, 1409usize, 0usize),
                    (0u32, 1409usize, 1usize),
                    (0u32, 1410usize, 1usize),
                    (0u32, 1411usize, 1usize),
                    (0u32, 1412usize, 0usize),
                    (0u32, 1412usize, 0usize),
                    (1342177238u32, 1412usize, 0usize),
                    (0u32, 1412usize, 2usize),
                    (0u32, 1414usize, 2usize),
                    (0u32, 1416usize, 1usize),
                    (0u32, 1417usize, 0usize),
                    (0u32, 1417usize, 0usize),
                    (1073741784u32, 1417usize, 0usize),
                    (0u32, 1417usize, 1usize),
                    (0u32, 1418usize, 2usize),
                    (0u32, 1420usize, 1usize),
                    (0u32, 1421usize, 0usize),
                    (0u32, 1421usize, 0usize),
                    (1073741816u32, 1421usize, 0usize),
                    (0u32, 1421usize, 2usize),
                    (0u32, 1423usize, 2usize),
                    (0u32, 1425usize, 1usize),
                    (0u32, 1426usize, 0usize),
                    (0u32, 1426usize, 0usize),
                    (1073741816u32, 1426usize, 0usize),
                    (0u32, 1426usize, 1usize),
                    (0u32, 1427usize, 1usize),
                    (0u32, 1428usize, 1usize),
                    (0u32, 1429usize, 0usize),
                    (0u32, 1429usize, 0usize),
                    (1342177238u32, 1429usize, 0usize),
                    (0u32, 1429usize, 2usize),
                    (0u32, 1431usize, 2usize),
                    (0u32, 1433usize, 1usize),
                    (0u32, 1434usize, 0usize),
                    (0u32, 1434usize, 0usize),
                    (1073741784u32, 1434usize, 0usize),
                    (0u32, 1434usize, 1usize),
                    (0u32, 1435usize, 2usize),
                    (0u32, 1437usize, 1usize),
                    (0u32, 1438usize, 0usize),
                    (0u32, 1438usize, 0usize),
                    (1073741816u32, 1438usize, 0usize),
                    (0u32, 1438usize, 2usize),
                    (0u32, 1440usize, 2usize),
                    (0u32, 1442usize, 1usize),
                    (0u32, 1443usize, 0usize),
                    (0u32, 1443usize, 0usize),
                    (1073741816u32, 1443usize, 0usize),
                    (0u32, 1443usize, 1usize),
                    (0u32, 1444usize, 1usize),
                    (0u32, 1445usize, 1usize),
                    (0u32, 1446usize, 0usize),
                    (0u32, 1446usize, 0usize),
                    (1342177238u32, 1446usize, 0usize),
                    (0u32, 1446usize, 2usize),
                    (0u32, 1448usize, 2usize),
                    (0u32, 1450usize, 1usize),
                    (0u32, 1451usize, 0usize),
                    (0u32, 1451usize, 0usize),
                    (1073741784u32, 1451usize, 0usize),
                    (0u32, 1451usize, 1usize),
                    (0u32, 1452usize, 2usize),
                    (0u32, 1454usize, 1usize),
                    (0u32, 1455usize, 0usize),
                    (0u32, 1455usize, 0usize),
                    (1073741816u32, 1455usize, 0usize),
                    (0u32, 1455usize, 2usize),
                    (0u32, 1457usize, 2usize),
                    (0u32, 1459usize, 1usize),
                    (0u32, 1460usize, 0usize),
                    (0u32, 1460usize, 0usize),
                    (1073741816u32, 1460usize, 0usize),
                    (0u32, 1460usize, 1usize),
                    (0u32, 1461usize, 1usize),
                    (0u32, 1462usize, 1usize),
                    (0u32, 1463usize, 0usize),
                    (0u32, 1463usize, 0usize),
                    (1342177238u32, 1463usize, 0usize),
                    (0u32, 1463usize, 2usize),
                    (0u32, 1465usize, 2usize),
                    (0u32, 1467usize, 1usize),
                    (0u32, 1468usize, 0usize),
                    (0u32, 1468usize, 0usize),
                    (1073741784u32, 1468usize, 0usize),
                    (0u32, 1468usize, 1usize),
                    (0u32, 1469usize, 2usize),
                    (0u32, 1471usize, 1usize),
                    (0u32, 1472usize, 0usize),
                    (0u32, 1472usize, 0usize),
                    (1073741816u32, 1472usize, 0usize),
                    (0u32, 1472usize, 2usize),
                    (0u32, 1474usize, 2usize),
                    (0u32, 1476usize, 1usize),
                    (0u32, 1477usize, 0usize),
                    (0u32, 1477usize, 0usize),
                    (1073741816u32, 1477usize, 0usize),
                    (0u32, 1477usize, 1usize),
                    (0u32, 1478usize, 1usize),
                    (0u32, 1479usize, 1usize),
                    (0u32, 1480usize, 0usize),
                    (0u32, 1480usize, 0usize),
                    (1342177238u32, 1480usize, 0usize),
                    (0u32, 1480usize, 2usize),
                    (0u32, 1482usize, 2usize),
                    (0u32, 1484usize, 1usize),
                    (0u32, 1485usize, 0usize),
                    (0u32, 1485usize, 0usize),
                    (1073741784u32, 1485usize, 0usize),
                    (0u32, 1485usize, 1usize),
                    (0u32, 1486usize, 2usize),
                    (0u32, 1488usize, 1usize),
                    (0u32, 1489usize, 0usize),
                    (0u32, 1489usize, 0usize),
                    (1073741816u32, 1489usize, 0usize),
                    (0u32, 1489usize, 2usize),
                    (0u32, 1491usize, 2usize),
                    (0u32, 1493usize, 1usize),
                    (0u32, 1494usize, 0usize),
                    (0u32, 1494usize, 0usize),
                    (1073741816u32, 1494usize, 0usize),
                    (0u32, 1494usize, 1usize),
                    (0u32, 1495usize, 1usize),
                    (0u32, 1496usize, 1usize),
                    (0u32, 1497usize, 0usize),
                    (0u32, 1497usize, 0usize),
                    (1342177238u32, 1497usize, 0usize),
                    (0u32, 1497usize, 2usize),
                    (0u32, 1499usize, 2usize),
                    (0u32, 1501usize, 1usize),
                    (0u32, 1502usize, 0usize),
                    (0u32, 1502usize, 0usize),
                    (1073741784u32, 1502usize, 0usize),
                    (0u32, 1502usize, 1usize),
                    (0u32, 1503usize, 2usize),
                    (0u32, 1505usize, 1usize),
                    (0u32, 1506usize, 0usize),
                    (0u32, 1506usize, 0usize),
                    (1073741816u32, 1506usize, 0usize),
                    (0u32, 1506usize, 2usize),
                    (0u32, 1508usize, 2usize),
                    (0u32, 1510usize, 1usize),
                    (0u32, 1511usize, 0usize),
                    (0u32, 1511usize, 0usize),
                    (1073741816u32, 1511usize, 0usize),
                    (0u32, 1511usize, 1usize),
                    (0u32, 1512usize, 1usize),
                    (0u32, 1513usize, 1usize),
                    (0u32, 1514usize, 0usize),
                    (0u32, 1514usize, 0usize),
                    (1342177238u32, 1514usize, 0usize),
                    (0u32, 1514usize, 2usize),
                    (0u32, 1516usize, 2usize),
                    (0u32, 1518usize, 1usize),
                    (0u32, 1519usize, 0usize),
                    (0u32, 1519usize, 0usize),
                    (1073741784u32, 1519usize, 0usize),
                    (0u32, 1519usize, 1usize),
                    (0u32, 1520usize, 2usize),
                    (0u32, 1522usize, 1usize),
                    (0u32, 1523usize, 0usize),
                    (0u32, 1523usize, 0usize),
                    (1073741816u32, 1523usize, 0usize),
                ];
                const VL_TERMS: [(u32, usize); 1523usize] = [
                    (268435454u32, 346usize),
                    (268435454u32, 342usize),
                    (268435454u32, 343usize),
                    (268435454u32, 348usize),
                    (16777216u32, 284usize),
                    (1996488705u32, 346usize),
                    (16777216u32, 241usize),
                    (16777216u32, 257usize),
                    (16777216u32, 310usize),
                    (1996488705u32, 342usize),
                    (1744831011u32, 343usize),
                    (268435454u32, 349usize),
                    (268435454u32, 347usize),
                    (268435454u32, 344usize),
                    (268435454u32, 345usize),
                    (268435454u32, 350usize),
                    (16777216u32, 285usize),
                    (1996488705u32, 347usize),
                    (16777216u32, 243usize),
                    (16777216u32, 259usize),
                    (16777216u32, 311usize),
                    (16777216u32, 343usize),
                    (1996488705u32, 344usize),
                    (1744831011u32, 345usize),
                    (268435454u32, 351usize),
                    (268435454u32, 359usize),
                    (268435454u32, 353usize),
                    (268435454u32, 362usize),
                    (268435454u32, 361usize),
                    (268435454u32, 356usize),
                    (268435454u32, 363usize),
                    (1048576u32, 257usize),
                    (2012217345u32, 358usize),
                    (2004877313u32, 359usize),
                    (268435454u32, 360usize),
                    (1048576u32, 272usize),
                    (1048576u32, 350usize),
                    (268435456u32, 351usize),
                    (2012217345u32, 352usize),
                    (2004877313u32, 353usize),
                    (1744830499u32, 354usize),
                    (268435454u32, 355usize),
                    (268435454u32, 364usize),
                    (1048576u32, 259usize),
                    (2012217345u32, 360usize),
                    (2004877313u32, 361usize),
                    (268435454u32, 358usize),
                    (1048576u32, 273usize),
                    (1048576u32, 348usize),
                    (268435456u32, 349usize),
                    (1048576u32, 354usize),
                    (2012217345u32, 355usize),
                    (2004877313u32, 356usize),
                    (1744830499u32, 357usize),
                    (268435454u32, 352usize),
                    (268435454u32, 365usize),
                    (268435454u32, 351usize),
                    (16777216u32, 241usize),
                    (16777216u32, 257usize),
                    (16777216u32, 310usize),
                    (16777216u32, 312usize),
                    (1744831011u32, 343usize),
                    (134217727u32, 363usize),
                    (16777216u32, 364usize),
                    (1996488705u32, 366usize),
                    (1744831011u32, 367usize),
                    (268435454u32, 370usize),
                    (268435454u32, 349usize),
                    (16777216u32, 243usize),
                    (16777216u32, 259usize),
                    (16777216u32, 311usize),
                    (16777216u32, 313usize),
                    (16777216u32, 343usize),
                    (1744831011u32, 345usize),
                    (134217727u32, 362usize),
                    (16777216u32, 365usize),
                    (16777216u32, 367usize),
                    (1996488705u32, 368usize),
                    (1744831011u32, 369usize),
                    (268435454u32, 371usize),
                    (268435454u32, 350usize),
                    (268435454u32, 366usize),
                    (268435454u32, 367usize),
                    (268435454u32, 372usize),
                    (268435454u32, 348usize),
                    (268435454u32, 368usize),
                    (268435454u32, 369usize),
                    (268435454u32, 373usize),
                    (268435454u32, 363usize),
                    (33554432u32, 272usize),
                    (33554432u32, 350usize),
                    (536870908u32, 351usize),
                    (1476396101u32, 354usize),
                    (33554432u32, 370usize),
                    (536870908u32, 373usize),
                    (1979711489u32, 374usize),
                    (1476396101u32, 375usize),
                    (268435454u32, 378usize),
                    (268435454u32, 362usize),
                    (33554432u32, 273usize),
                    (33554432u32, 348usize),
                    (536870908u32, 349usize),
                    (33554432u32, 354usize),
                    (1476396101u32, 357usize),
                    (33554432u32, 371usize),
                    (536870908u32, 372usize),
                    (33554432u32, 375usize),
                    (1979711489u32, 376usize),
                    (1476396101u32, 377usize),
                    (268435454u32, 379usize),
                    (268435454u32, 364usize),
                    (268435454u32, 374usize),
                    (268435454u32, 380usize),
                    (268435454u32, 365usize),
                    (268435454u32, 376usize),
                    (268435454u32, 381usize),
                    (268435454u32, 386usize),
                    (268435454u32, 382usize),
                    (268435454u32, 383usize),
                    (268435454u32, 388usize),
                    (16777216u32, 280usize),
                    (1996488705u32, 386usize),
                    (16777216u32, 245usize),
                    (16777216u32, 261usize),
                    (16777216u32, 314usize),
                    (1996488705u32, 382usize),
                    (1744831011u32, 383usize),
                    (268435454u32, 389usize),
                    (268435454u32, 387usize),
                    (268435454u32, 384usize),
                    (268435454u32, 385usize),
                    (268435454u32, 390usize),
                    (16777216u32, 281usize),
                    (1996488705u32, 387usize),
                    (16777216u32, 247usize),
                    (16777216u32, 263usize),
                    (16777216u32, 315usize),
                    (16777216u32, 383usize),
                    (1996488705u32, 384usize),
                    (1744831011u32, 385usize),
                    (268435454u32, 391usize),
                    (268435454u32, 399usize),
                    (268435454u32, 393usize),
                    (268435454u32, 402usize),
                    (268435454u32, 401usize),
                    (268435454u32, 396usize),
                    (268435454u32, 403usize),
                    (1048576u32, 261usize),
                    (2012217345u32, 398usize),
                    (2004877313u32, 399usize),
                    (268435454u32, 400usize),
                    (1048576u32, 274usize),
                    (1048576u32, 390usize),
                    (268435456u32, 391usize),
                    (2012217345u32, 392usize),
                    (2004877313u32, 393usize),
                    (1744830499u32, 394usize),
                    (268435454u32, 395usize),
                    (268435454u32, 404usize),
                    (1048576u32, 263usize),
                    (2012217345u32, 400usize),
                    (2004877313u32, 401usize),
                    (268435454u32, 398usize),
                    (1048576u32, 275usize),
                    (1048576u32, 388usize),
                    (268435456u32, 389usize),
                    (1048576u32, 394usize),
                    (2012217345u32, 395usize),
                    (2004877313u32, 396usize),
                    (1744830499u32, 397usize),
                    (268435454u32, 392usize),
                    (268435454u32, 405usize),
                    (268435454u32, 391usize),
                    (16777216u32, 245usize),
                    (16777216u32, 261usize),
                    (16777216u32, 314usize),
                    (16777216u32, 316usize),
                    (1744831011u32, 383usize),
                    (134217727u32, 403usize),
                    (16777216u32, 404usize),
                    (1996488705u32, 406usize),
                    (1744831011u32, 407usize),
                    (268435454u32, 410usize),
                    (268435454u32, 389usize),
                    (16777216u32, 247usize),
                    (16777216u32, 263usize),
                    (16777216u32, 315usize),
                    (16777216u32, 317usize),
                    (16777216u32, 383usize),
                    (1744831011u32, 385usize),
                    (134217727u32, 402usize),
                    (16777216u32, 405usize),
                    (16777216u32, 407usize),
                    (1996488705u32, 408usize),
                    (1744831011u32, 409usize),
                    (268435454u32, 411usize),
                    (268435454u32, 390usize),
                    (268435454u32, 406usize),
                    (268435454u32, 407usize),
                    (268435454u32, 412usize),
                    (268435454u32, 388usize),
                    (268435454u32, 408usize),
                    (268435454u32, 409usize),
                    (268435454u32, 413usize),
                    (268435454u32, 403usize),
                    (33554432u32, 274usize),
                    (33554432u32, 390usize),
                    (536870908u32, 391usize),
                    (1476396101u32, 394usize),
                    (33554432u32, 410usize),
                    (536870908u32, 413usize),
                    (1979711489u32, 414usize),
                    (1476396101u32, 415usize),
                    (268435454u32, 418usize),
                    (268435454u32, 402usize),
                    (33554432u32, 275usize),
                    (33554432u32, 388usize),
                    (536870908u32, 389usize),
                    (33554432u32, 394usize),
                    (1476396101u32, 397usize),
                    (33554432u32, 411usize),
                    (536870908u32, 412usize),
                    (33554432u32, 415usize),
                    (1979711489u32, 416usize),
                    (1476396101u32, 417usize),
                    (268435454u32, 419usize),
                    (268435454u32, 404usize),
                    (268435454u32, 414usize),
                    (268435454u32, 420usize),
                    (268435454u32, 405usize),
                    (268435454u32, 416usize),
                    (268435454u32, 421usize),
                    (268435454u32, 426usize),
                    (268435454u32, 422usize),
                    (268435454u32, 423usize),
                    (268435454u32, 428usize),
                    (16777216u32, 286usize),
                    (1996488705u32, 426usize),
                    (16777216u32, 249usize),
                    (16777216u32, 265usize),
                    (16777216u32, 318usize),
                    (1996488705u32, 422usize),
                    (1744831011u32, 423usize),
                    (268435454u32, 429usize),
                    (268435454u32, 427usize),
                    (268435454u32, 424usize),
                    (268435454u32, 425usize),
                    (268435454u32, 430usize),
                    (16777216u32, 287usize),
                    (1996488705u32, 427usize),
                    (16777216u32, 251usize),
                    (16777216u32, 267usize),
                    (16777216u32, 319usize),
                    (16777216u32, 423usize),
                    (1996488705u32, 424usize),
                    (1744831011u32, 425usize),
                    (268435454u32, 431usize),
                    (268435454u32, 439usize),
                    (268435454u32, 433usize),
                    (268435454u32, 442usize),
                    (268435454u32, 441usize),
                    (268435454u32, 436usize),
                    (268435454u32, 443usize),
                    (1048576u32, 265usize),
                    (2012217345u32, 438usize),
                    (2004877313u32, 439usize),
                    (268435454u32, 440usize),
                    (1048576u32, 276usize),
                    (1048576u32, 430usize),
                    (268435456u32, 431usize),
                    (2012217345u32, 432usize),
                    (2004877313u32, 433usize),
                    (1744830499u32, 434usize),
                    (268435454u32, 435usize),
                    (268435454u32, 444usize),
                    (1048576u32, 267usize),
                    (2012217345u32, 440usize),
                    (2004877313u32, 441usize),
                    (268435454u32, 438usize),
                    (1048576u32, 277usize),
                    (1048576u32, 428usize),
                    (268435456u32, 429usize),
                    (1048576u32, 434usize),
                    (2012217345u32, 435usize),
                    (2004877313u32, 436usize),
                    (1744830499u32, 437usize),
                    (268435454u32, 432usize),
                    (268435454u32, 445usize),
                    (268435454u32, 431usize),
                    (16777216u32, 249usize),
                    (16777216u32, 265usize),
                    (16777216u32, 318usize),
                    (16777216u32, 320usize),
                    (1744831011u32, 423usize),
                    (134217727u32, 443usize),
                    (16777216u32, 444usize),
                    (1996488705u32, 446usize),
                    (1744831011u32, 447usize),
                    (268435454u32, 450usize),
                    (268435454u32, 429usize),
                    (16777216u32, 251usize),
                    (16777216u32, 267usize),
                    (16777216u32, 319usize),
                    (16777216u32, 321usize),
                    (16777216u32, 423usize),
                    (1744831011u32, 425usize),
                    (134217727u32, 442usize),
                    (16777216u32, 445usize),
                    (16777216u32, 447usize),
                    (1996488705u32, 448usize),
                    (1744831011u32, 449usize),
                    (268435454u32, 451usize),
                    (268435454u32, 430usize),
                    (268435454u32, 446usize),
                    (268435454u32, 447usize),
                    (268435454u32, 452usize),
                    (268435454u32, 428usize),
                    (268435454u32, 448usize),
                    (268435454u32, 449usize),
                    (268435454u32, 453usize),
                    (268435454u32, 443usize),
                    (33554432u32, 276usize),
                    (33554432u32, 430usize),
                    (536870908u32, 431usize),
                    (1476396101u32, 434usize),
                    (33554432u32, 450usize),
                    (536870908u32, 453usize),
                    (1979711489u32, 454usize),
                    (1476396101u32, 455usize),
                    (268435454u32, 458usize),
                    (268435454u32, 442usize),
                    (33554432u32, 277usize),
                    (33554432u32, 428usize),
                    (536870908u32, 429usize),
                    (33554432u32, 434usize),
                    (1476396101u32, 437usize),
                    (33554432u32, 451usize),
                    (536870908u32, 452usize),
                    (33554432u32, 455usize),
                    (1979711489u32, 456usize),
                    (1476396101u32, 457usize),
                    (268435454u32, 459usize),
                    (268435454u32, 444usize),
                    (268435454u32, 454usize),
                    (268435454u32, 460usize),
                    (268435454u32, 445usize),
                    (268435454u32, 456usize),
                    (268435454u32, 461usize),
                    (268435454u32, 466usize),
                    (268435454u32, 462usize),
                    (268435454u32, 463usize),
                    (268435454u32, 468usize),
                    (16777216u32, 282usize),
                    (1996488705u32, 466usize),
                    (16777216u32, 253usize),
                    (16777216u32, 269usize),
                    (16777216u32, 322usize),
                    (1996488705u32, 462usize),
                    (1744831011u32, 463usize),
                    (268435454u32, 469usize),
                    (268435454u32, 467usize),
                    (268435454u32, 464usize),
                    (268435454u32, 465usize),
                    (268435454u32, 470usize),
                    (16777216u32, 283usize),
                    (1996488705u32, 467usize),
                    (16777216u32, 255usize),
                    (16777216u32, 271usize),
                    (16777216u32, 323usize),
                    (16777216u32, 463usize),
                    (1996488705u32, 464usize),
                    (1744831011u32, 465usize),
                    (268435454u32, 471usize),
                    (268435454u32, 479usize),
                    (268435454u32, 473usize),
                    (268435454u32, 482usize),
                    (268435454u32, 481usize),
                    (268435454u32, 476usize),
                    (268435454u32, 483usize),
                    (1048576u32, 269usize),
                    (2012217345u32, 478usize),
                    (2004877313u32, 479usize),
                    (268435454u32, 480usize),
                    (1048576u32, 278usize),
                    (1048576u32, 470usize),
                    (268435456u32, 471usize),
                    (2012217345u32, 472usize),
                    (2004877313u32, 473usize),
                    (1744830499u32, 474usize),
                    (268435454u32, 475usize),
                    (268435454u32, 484usize),
                    (1048576u32, 271usize),
                    (2012217345u32, 480usize),
                    (2004877313u32, 481usize),
                    (268435454u32, 478usize),
                    (1048576u32, 279usize),
                    (1048576u32, 468usize),
                    (268435456u32, 469usize),
                    (1048576u32, 474usize),
                    (2012217345u32, 475usize),
                    (2004877313u32, 476usize),
                    (1744830499u32, 477usize),
                    (268435454u32, 472usize),
                    (268435454u32, 485usize),
                    (268435454u32, 471usize),
                    (16777216u32, 253usize),
                    (16777216u32, 269usize),
                    (16777216u32, 322usize),
                    (16777216u32, 324usize),
                    (1744831011u32, 463usize),
                    (134217727u32, 483usize),
                    (16777216u32, 484usize),
                    (1996488705u32, 486usize),
                    (1744831011u32, 487usize),
                    (268435454u32, 490usize),
                    (268435454u32, 469usize),
                    (16777216u32, 255usize),
                    (16777216u32, 271usize),
                    (16777216u32, 323usize),
                    (16777216u32, 325usize),
                    (16777216u32, 463usize),
                    (1744831011u32, 465usize),
                    (134217727u32, 482usize),
                    (16777216u32, 485usize),
                    (16777216u32, 487usize),
                    (1996488705u32, 488usize),
                    (1744831011u32, 489usize),
                    (268435454u32, 491usize),
                    (268435454u32, 470usize),
                    (268435454u32, 486usize),
                    (268435454u32, 487usize),
                    (268435454u32, 492usize),
                    (268435454u32, 468usize),
                    (268435454u32, 488usize),
                    (268435454u32, 489usize),
                    (268435454u32, 493usize),
                    (268435454u32, 483usize),
                    (33554432u32, 278usize),
                    (33554432u32, 470usize),
                    (536870908u32, 471usize),
                    (1476396101u32, 474usize),
                    (33554432u32, 490usize),
                    (536870908u32, 493usize),
                    (1979711489u32, 494usize),
                    (1476396101u32, 495usize),
                    (268435454u32, 498usize),
                    (268435454u32, 482usize),
                    (33554432u32, 279usize),
                    (33554432u32, 468usize),
                    (536870908u32, 469usize),
                    (33554432u32, 474usize),
                    (1476396101u32, 477usize),
                    (33554432u32, 491usize),
                    (536870908u32, 492usize),
                    (33554432u32, 495usize),
                    (1979711489u32, 496usize),
                    (1476396101u32, 497usize),
                    (268435454u32, 499usize),
                    (268435454u32, 484usize),
                    (268435454u32, 494usize),
                    (268435454u32, 500usize),
                    (268435454u32, 485usize),
                    (268435454u32, 496usize),
                    (268435454u32, 501usize),
                    (268435454u32, 490usize),
                    (268435454u32, 502usize),
                    (268435454u32, 503usize),
                    (268435454u32, 506usize),
                    (268435454u32, 493usize),
                    (16777216u32, 241usize),
                    (16777216u32, 257usize),
                    (16777216u32, 310usize),
                    (16777216u32, 312usize),
                    (16777216u32, 326usize),
                    (1744831011u32, 343usize),
                    (134217727u32, 363usize),
                    (16777216u32, 364usize),
                    (1744831011u32, 367usize),
                    (16777216u32, 418usize),
                    (536870908u32, 421usize),
                    (1996488705u32, 502usize),
                    (1744831011u32, 503usize),
                    (268435454u32, 507usize),
                    (268435454u32, 491usize),
                    (268435454u32, 504usize),
                    (268435454u32, 505usize),
                    (268435454u32, 508usize),
                    (268435454u32, 492usize),
                    (16777216u32, 243usize),
                    (16777216u32, 259usize),
                    (16777216u32, 311usize),
                    (16777216u32, 313usize),
                    (16777216u32, 327usize),
                    (16777216u32, 343usize),
                    (1744831011u32, 345usize),
                    (134217727u32, 362usize),
                    (16777216u32, 365usize),
                    (16777216u32, 367usize),
                    (1744831011u32, 369usize),
                    (16777216u32, 419usize),
                    (536870908u32, 420usize),
                    (16777216u32, 503usize),
                    (1996488705u32, 504usize),
                    (1744831011u32, 505usize),
                    (268435454u32, 509usize),
                    (268435454u32, 517usize),
                    (268435454u32, 511usize),
                    (268435454u32, 520usize),
                    (268435454u32, 519usize),
                    (268435454u32, 514usize),
                    (268435454u32, 521usize),
                    (1048576u32, 418usize),
                    (536870912u32, 421usize),
                    (2012217345u32, 516usize),
                    (2004877313u32, 517usize),
                    (268435454u32, 518usize),
                    (1048576u32, 276usize),
                    (1048576u32, 430usize),
                    (268435456u32, 431usize),
                    (1744830499u32, 434usize),
                    (1048576u32, 450usize),
                    (268435456u32, 453usize),
                    (1744830499u32, 455usize),
                    (1048576u32, 508usize),
                    (268435456u32, 509usize),
                    (2012217345u32, 510usize),
                    (2004877313u32, 511usize),
                    (1744830499u32, 512usize),
                    (268435454u32, 513usize),
                    (268435454u32, 522usize),
                    (1048576u32, 419usize),
                    (536870912u32, 420usize),
                    (2012217345u32, 518usize),
                    (2004877313u32, 519usize),
                    (268435454u32, 516usize),
                    (1048576u32, 277usize),
                    (1048576u32, 428usize),
                    (268435456u32, 429usize),
                    (1048576u32, 434usize),
                    (1744830499u32, 437usize),
                    (1048576u32, 451usize),
                    (268435456u32, 452usize),
                    (1048576u32, 455usize),
                    (1744830499u32, 457usize),
                    (1048576u32, 506usize),
                    (268435456u32, 507usize),
                    (1048576u32, 512usize),
                    (2012217345u32, 513usize),
                    (2004877313u32, 514usize),
                    (1744830499u32, 515usize),
                    (268435454u32, 510usize),
                    (268435454u32, 523usize),
                    (268435454u32, 509usize),
                    (16777216u32, 56usize),
                    (1996488705u32, 524usize),
                    (268435454u32, 526usize),
                    (268435454u32, 507usize),
                    (16777216u32, 57usize),
                    (1996488705u32, 525usize),
                    (268435454u32, 527usize),
                    (268435454u32, 508usize),
                    (268435454u32, 524usize),
                    (2013200385u32, 56usize),
                    (65536u32, 241usize),
                    (65536u32, 257usize),
                    (65536u32, 310usize),
                    (65536u32, 312usize),
                    (65536u32, 326usize),
                    (65536u32, 328usize),
                    (1744830467u32, 343usize),
                    (8388608u32, 363usize),
                    (65536u32, 364usize),
                    (1744830467u32, 367usize),
                    (65536u32, 418usize),
                    (33554432u32, 421usize),
                    (1744830467u32, 503usize),
                    (8388608u32, 521usize),
                    (65536u32, 522usize),
                    (16777216u32, 147usize),
                    (1996488705u32, 527usize),
                    (268435454u32, 506usize),
                    (268435454u32, 525usize),
                    (2013265920u32, 56usize),
                    (2013200385u32, 57usize),
                    (1u32, 241usize),
                    (65536u32, 243usize),
                    (1u32, 257usize),
                    (65536u32, 259usize),
                    (1u32, 310usize),
                    (65536u32, 311usize),
                    (1u32, 312usize),
                    (65536u32, 313usize),
                    (1u32, 326usize),
                    (65536u32, 327usize),
                    (1u32, 328usize),
                    (65536u32, 329usize),
                    (1744830467u32, 345usize),
                    (8388608u32, 362usize),
                    (128u32, 363usize),
                    (1u32, 364usize),
                    (65536u32, 365usize),
                    (1744830467u32, 369usize),
                    (1u32, 418usize),
                    (65536u32, 419usize),
                    (33554432u32, 420usize),
                    (512u32, 421usize),
                    (1744830467u32, 505usize),
                    (8388608u32, 520usize),
                    (128u32, 521usize),
                    (1u32, 522usize),
                    (65536u32, 523usize),
                    (16777216u32, 146usize),
                    (1996488705u32, 526usize),
                    (268435454u32, 521usize),
                    (33554432u32, 116usize),
                    (1979711489u32, 528usize),
                    (268435454u32, 530usize),
                    (268435454u32, 520usize),
                    (33554432u32, 117usize),
                    (1979711489u32, 529usize),
                    (268435454u32, 531usize),
                    (268435454u32, 522usize),
                    (268435454u32, 528usize),
                    (2013200385u32, 116usize),
                    (65536u32, 146usize),
                    (65536u32, 276usize),
                    (65536u32, 430usize),
                    (16777216u32, 431usize),
                    (1744830467u32, 434usize),
                    (65536u32, 450usize),
                    (16777216u32, 453usize),
                    (1744830467u32, 455usize),
                    (65536u32, 508usize),
                    (16777216u32, 509usize),
                    (1744830467u32, 512usize),
                    (8388608u32, 87usize),
                    (2004877313u32, 531usize),
                    (268435454u32, 523usize),
                    (268435454u32, 529usize),
                    (2013265920u32, 116usize),
                    (2013200385u32, 117usize),
                    (1u32, 146usize),
                    (65536u32, 147usize),
                    (1u32, 276usize),
                    (65536u32, 277usize),
                    (65536u32, 428usize),
                    (16777216u32, 429usize),
                    (1u32, 430usize),
                    (256u32, 431usize),
                    (1744830467u32, 437usize),
                    (1u32, 450usize),
                    (65536u32, 451usize),
                    (16777216u32, 452usize),
                    (256u32, 453usize),
                    (1744830467u32, 457usize),
                    (65536u32, 506usize),
                    (16777216u32, 507usize),
                    (1u32, 508usize),
                    (256u32, 509usize),
                    (1744830467u32, 515usize),
                    (8388608u32, 86usize),
                    (2004877313u32, 530usize),
                    (268435454u32, 370usize),
                    (268435454u32, 532usize),
                    (268435454u32, 533usize),
                    (268435454u32, 536usize),
                    (268435454u32, 373usize),
                    (16777216u32, 245usize),
                    (16777216u32, 261usize),
                    (16777216u32, 314usize),
                    (16777216u32, 316usize),
                    (16777216u32, 330usize),
                    (1744831011u32, 383usize),
                    (134217727u32, 403usize),
                    (16777216u32, 404usize),
                    (1744831011u32, 407usize),
                    (16777216u32, 458usize),
                    (536870908u32, 461usize),
                    (1996488705u32, 532usize),
                    (1744831011u32, 533usize),
                    (268435454u32, 537usize),
                    (268435454u32, 371usize),
                    (268435454u32, 534usize),
                    (268435454u32, 535usize),
                    (268435454u32, 538usize),
                    (268435454u32, 372usize),
                    (16777216u32, 247usize),
                    (16777216u32, 263usize),
                    (16777216u32, 315usize),
                    (16777216u32, 317usize),
                    (16777216u32, 331usize),
                    (16777216u32, 383usize),
                    (1744831011u32, 385usize),
                    (134217727u32, 402usize),
                    (16777216u32, 405usize),
                    (16777216u32, 407usize),
                    (1744831011u32, 409usize),
                    (16777216u32, 459usize),
                    (536870908u32, 460usize),
                    (16777216u32, 533usize),
                    (1996488705u32, 534usize),
                    (1744831011u32, 535usize),
                    (268435454u32, 539usize),
                    (268435454u32, 547usize),
                    (268435454u32, 541usize),
                    (268435454u32, 550usize),
                    (268435454u32, 549usize),
                    (268435454u32, 544usize),
                    (268435454u32, 551usize),
                    (1048576u32, 458usize),
                    (536870912u32, 461usize),
                    (2012217345u32, 546usize),
                    (2004877313u32, 547usize),
                    (268435454u32, 548usize),
                    (1048576u32, 278usize),
                    (1048576u32, 470usize),
                    (268435456u32, 471usize),
                    (1744830499u32, 474usize),
                    (1048576u32, 490usize),
                    (268435456u32, 493usize),
                    (1744830499u32, 495usize),
                    (1048576u32, 538usize),
                    (268435456u32, 539usize),
                    (2012217345u32, 540usize),
                    (2004877313u32, 541usize),
                    (1744830499u32, 542usize),
                    (268435454u32, 543usize),
                    (268435454u32, 552usize),
                    (1048576u32, 459usize),
                    (536870912u32, 460usize),
                    (2012217345u32, 548usize),
                    (2004877313u32, 549usize),
                    (268435454u32, 546usize),
                    (1048576u32, 279usize),
                    (1048576u32, 468usize),
                    (268435456u32, 469usize),
                    (1048576u32, 474usize),
                    (1744830499u32, 477usize),
                    (1048576u32, 491usize),
                    (268435456u32, 492usize),
                    (1048576u32, 495usize),
                    (1744830499u32, 497usize),
                    (1048576u32, 536usize),
                    (268435456u32, 537usize),
                    (1048576u32, 542usize),
                    (2012217345u32, 543usize),
                    (2004877313u32, 544usize),
                    (1744830499u32, 545usize),
                    (268435454u32, 540usize),
                    (268435454u32, 553usize),
                    (268435454u32, 539usize),
                    (16777216u32, 62usize),
                    (1996488705u32, 554usize),
                    (268435454u32, 556usize),
                    (268435454u32, 537usize),
                    (16777216u32, 63usize),
                    (1996488705u32, 555usize),
                    (268435454u32, 557usize),
                    (268435454u32, 538usize),
                    (268435454u32, 554usize),
                    (2013200385u32, 62usize),
                    (65536u32, 245usize),
                    (65536u32, 261usize),
                    (65536u32, 314usize),
                    (65536u32, 316usize),
                    (65536u32, 330usize),
                    (65536u32, 332usize),
                    (1744830467u32, 383usize),
                    (8388608u32, 403usize),
                    (65536u32, 404usize),
                    (1744830467u32, 407usize),
                    (65536u32, 458usize),
                    (33554432u32, 461usize),
                    (1744830467u32, 533usize),
                    (8388608u32, 551usize),
                    (65536u32, 552usize),
                    (16777216u32, 129usize),
                    (1996488705u32, 557usize),
                    (268435454u32, 536usize),
                    (268435454u32, 555usize),
                    (2013265920u32, 62usize),
                    (2013200385u32, 63usize),
                    (1u32, 245usize),
                    (65536u32, 247usize),
                    (1u32, 261usize),
                    (65536u32, 263usize),
                    (1u32, 314usize),
                    (65536u32, 315usize),
                    (1u32, 316usize),
                    (65536u32, 317usize),
                    (1u32, 330usize),
                    (65536u32, 331usize),
                    (1u32, 332usize),
                    (65536u32, 333usize),
                    (1744830467u32, 385usize),
                    (8388608u32, 402usize),
                    (128u32, 403usize),
                    (1u32, 404usize),
                    (65536u32, 405usize),
                    (1744830467u32, 409usize),
                    (1u32, 458usize),
                    (65536u32, 459usize),
                    (33554432u32, 460usize),
                    (512u32, 461usize),
                    (1744830467u32, 535usize),
                    (8388608u32, 550usize),
                    (128u32, 551usize),
                    (1u32, 552usize),
                    (65536u32, 553usize),
                    (16777216u32, 128usize),
                    (1996488705u32, 556usize),
                    (268435454u32, 551usize),
                    (33554432u32, 122usize),
                    (1979711489u32, 558usize),
                    (268435454u32, 560usize),
                    (268435454u32, 550usize),
                    (33554432u32, 123usize),
                    (1979711489u32, 559usize),
                    (268435454u32, 561usize),
                    (268435454u32, 552usize),
                    (268435454u32, 558usize),
                    (2013200385u32, 122usize),
                    (65536u32, 128usize),
                    (65536u32, 278usize),
                    (65536u32, 470usize),
                    (16777216u32, 471usize),
                    (1744830467u32, 474usize),
                    (65536u32, 490usize),
                    (16777216u32, 493usize),
                    (1744830467u32, 495usize),
                    (65536u32, 538usize),
                    (16777216u32, 539usize),
                    (1744830467u32, 542usize),
                    (8388608u32, 93usize),
                    (2004877313u32, 561usize),
                    (268435454u32, 553usize),
                    (268435454u32, 559usize),
                    (2013265920u32, 122usize),
                    (2013200385u32, 123usize),
                    (1u32, 128usize),
                    (65536u32, 129usize),
                    (1u32, 278usize),
                    (65536u32, 279usize),
                    (65536u32, 468usize),
                    (16777216u32, 469usize),
                    (1u32, 470usize),
                    (256u32, 471usize),
                    (1744830467u32, 477usize),
                    (1u32, 490usize),
                    (65536u32, 491usize),
                    (16777216u32, 492usize),
                    (256u32, 493usize),
                    (1744830467u32, 497usize),
                    (65536u32, 536usize),
                    (16777216u32, 537usize),
                    (1u32, 538usize),
                    (256u32, 539usize),
                    (1744830467u32, 545usize),
                    (8388608u32, 92usize),
                    (2004877313u32, 560usize),
                    (268435454u32, 410usize),
                    (268435454u32, 562usize),
                    (268435454u32, 563usize),
                    (268435454u32, 566usize),
                    (268435454u32, 413usize),
                    (16777216u32, 249usize),
                    (16777216u32, 265usize),
                    (16777216u32, 318usize),
                    (16777216u32, 320usize),
                    (16777216u32, 334usize),
                    (1744831011u32, 423usize),
                    (134217727u32, 443usize),
                    (16777216u32, 444usize),
                    (1744831011u32, 447usize),
                    (16777216u32, 498usize),
                    (536870908u32, 501usize),
                    (1996488705u32, 562usize),
                    (1744831011u32, 563usize),
                    (268435454u32, 567usize),
                    (268435454u32, 411usize),
                    (268435454u32, 564usize),
                    (268435454u32, 565usize),
                    (268435454u32, 568usize),
                    (268435454u32, 412usize),
                    (16777216u32, 251usize),
                    (16777216u32, 267usize),
                    (16777216u32, 319usize),
                    (16777216u32, 321usize),
                    (16777216u32, 335usize),
                    (16777216u32, 423usize),
                    (1744831011u32, 425usize),
                    (134217727u32, 442usize),
                    (16777216u32, 445usize),
                    (16777216u32, 447usize),
                    (1744831011u32, 449usize),
                    (16777216u32, 499usize),
                    (536870908u32, 500usize),
                    (16777216u32, 563usize),
                    (1996488705u32, 564usize),
                    (1744831011u32, 565usize),
                    (268435454u32, 569usize),
                    (268435454u32, 577usize),
                    (268435454u32, 571usize),
                    (268435454u32, 580usize),
                    (268435454u32, 579usize),
                    (268435454u32, 574usize),
                    (268435454u32, 581usize),
                    (1048576u32, 498usize),
                    (536870912u32, 501usize),
                    (2012217345u32, 576usize),
                    (2004877313u32, 577usize),
                    (268435454u32, 578usize),
                    (1048576u32, 272usize),
                    (1048576u32, 350usize),
                    (268435456u32, 351usize),
                    (1744830499u32, 354usize),
                    (1048576u32, 370usize),
                    (268435456u32, 373usize),
                    (1744830499u32, 375usize),
                    (1048576u32, 568usize),
                    (268435456u32, 569usize),
                    (2012217345u32, 570usize),
                    (2004877313u32, 571usize),
                    (1744830499u32, 572usize),
                    (268435454u32, 573usize),
                    (268435454u32, 582usize),
                    (1048576u32, 499usize),
                    (536870912u32, 500usize),
                    (2012217345u32, 578usize),
                    (2004877313u32, 579usize),
                    (268435454u32, 576usize),
                    (1048576u32, 273usize),
                    (1048576u32, 348usize),
                    (268435456u32, 349usize),
                    (1048576u32, 354usize),
                    (1744830499u32, 357usize),
                    (1048576u32, 371usize),
                    (268435456u32, 372usize),
                    (1048576u32, 375usize),
                    (1744830499u32, 377usize),
                    (1048576u32, 566usize),
                    (268435456u32, 567usize),
                    (1048576u32, 572usize),
                    (2012217345u32, 573usize),
                    (2004877313u32, 574usize),
                    (1744830499u32, 575usize),
                    (268435454u32, 570usize),
                    (268435454u32, 583usize),
                    (268435454u32, 569usize),
                    (16777216u32, 68usize),
                    (1996488705u32, 584usize),
                    (268435454u32, 586usize),
                    (268435454u32, 567usize),
                    (16777216u32, 69usize),
                    (1996488705u32, 585usize),
                    (268435454u32, 587usize),
                    (268435454u32, 568usize),
                    (268435454u32, 584usize),
                    (2013200385u32, 68usize),
                    (65536u32, 249usize),
                    (65536u32, 265usize),
                    (65536u32, 318usize),
                    (65536u32, 320usize),
                    (65536u32, 334usize),
                    (65536u32, 336usize),
                    (1744830467u32, 423usize),
                    (8388608u32, 443usize),
                    (65536u32, 444usize),
                    (1744830467u32, 447usize),
                    (65536u32, 498usize),
                    (33554432u32, 501usize),
                    (1744830467u32, 563usize),
                    (8388608u32, 581usize),
                    (65536u32, 582usize),
                    (16777216u32, 135usize),
                    (1996488705u32, 587usize),
                    (268435454u32, 566usize),
                    (268435454u32, 585usize),
                    (2013265920u32, 68usize),
                    (2013200385u32, 69usize),
                    (1u32, 249usize),
                    (65536u32, 251usize),
                    (1u32, 265usize),
                    (65536u32, 267usize),
                    (1u32, 318usize),
                    (65536u32, 319usize),
                    (1u32, 320usize),
                    (65536u32, 321usize),
                    (1u32, 334usize),
                    (65536u32, 335usize),
                    (1u32, 336usize),
                    (65536u32, 337usize),
                    (1744830467u32, 425usize),
                    (8388608u32, 442usize),
                    (128u32, 443usize),
                    (1u32, 444usize),
                    (65536u32, 445usize),
                    (1744830467u32, 449usize),
                    (1u32, 498usize),
                    (65536u32, 499usize),
                    (33554432u32, 500usize),
                    (512u32, 501usize),
                    (1744830467u32, 565usize),
                    (8388608u32, 580usize),
                    (128u32, 581usize),
                    (1u32, 582usize),
                    (65536u32, 583usize),
                    (16777216u32, 134usize),
                    (1996488705u32, 586usize),
                    (268435454u32, 581usize),
                    (33554432u32, 104usize),
                    (1979711489u32, 588usize),
                    (268435454u32, 590usize),
                    (268435454u32, 580usize),
                    (33554432u32, 105usize),
                    (1979711489u32, 589usize),
                    (268435454u32, 591usize),
                    (268435454u32, 582usize),
                    (268435454u32, 588usize),
                    (2013200385u32, 104usize),
                    (65536u32, 134usize),
                    (65536u32, 272usize),
                    (65536u32, 350usize),
                    (16777216u32, 351usize),
                    (1744830467u32, 354usize),
                    (65536u32, 370usize),
                    (16777216u32, 373usize),
                    (1744830467u32, 375usize),
                    (65536u32, 568usize),
                    (16777216u32, 569usize),
                    (1744830467u32, 572usize),
                    (8388608u32, 99usize),
                    (2004877313u32, 591usize),
                    (268435454u32, 583usize),
                    (268435454u32, 589usize),
                    (2013265920u32, 104usize),
                    (2013200385u32, 105usize),
                    (1u32, 134usize),
                    (65536u32, 135usize),
                    (1u32, 272usize),
                    (65536u32, 273usize),
                    (65536u32, 348usize),
                    (16777216u32, 349usize),
                    (1u32, 350usize),
                    (256u32, 351usize),
                    (1744830467u32, 357usize),
                    (1u32, 370usize),
                    (65536u32, 371usize),
                    (16777216u32, 372usize),
                    (256u32, 373usize),
                    (1744830467u32, 377usize),
                    (65536u32, 566usize),
                    (16777216u32, 567usize),
                    (1u32, 568usize),
                    (256u32, 569usize),
                    (1744830467u32, 575usize),
                    (8388608u32, 98usize),
                    (2004877313u32, 590usize),
                    (268435454u32, 450usize),
                    (268435454u32, 592usize),
                    (268435454u32, 593usize),
                    (268435454u32, 596usize),
                    (268435454u32, 453usize),
                    (16777216u32, 253usize),
                    (16777216u32, 269usize),
                    (16777216u32, 322usize),
                    (16777216u32, 324usize),
                    (16777216u32, 338usize),
                    (16777216u32, 378usize),
                    (536870908u32, 381usize),
                    (1744831011u32, 463usize),
                    (134217727u32, 483usize),
                    (16777216u32, 484usize),
                    (1744831011u32, 487usize),
                    (1996488705u32, 592usize),
                    (1744831011u32, 593usize),
                    (268435454u32, 597usize),
                    (268435454u32, 451usize),
                    (268435454u32, 594usize),
                    (268435454u32, 595usize),
                    (268435454u32, 598usize),
                    (268435454u32, 452usize),
                    (16777216u32, 255usize),
                    (16777216u32, 271usize),
                    (16777216u32, 323usize),
                    (16777216u32, 325usize),
                    (16777216u32, 339usize),
                    (16777216u32, 379usize),
                    (536870908u32, 380usize),
                    (16777216u32, 463usize),
                    (1744831011u32, 465usize),
                    (134217727u32, 482usize),
                    (16777216u32, 485usize),
                    (16777216u32, 487usize),
                    (1744831011u32, 489usize),
                    (16777216u32, 593usize),
                    (1996488705u32, 594usize),
                    (1744831011u32, 595usize),
                    (268435454u32, 599usize),
                    (268435454u32, 607usize),
                    (268435454u32, 601usize),
                    (268435454u32, 610usize),
                    (268435454u32, 609usize),
                    (268435454u32, 604usize),
                    (268435454u32, 611usize),
                    (1048576u32, 378usize),
                    (536870912u32, 381usize),
                    (2012217345u32, 606usize),
                    (2004877313u32, 607usize),
                    (268435454u32, 608usize),
                    (1048576u32, 274usize),
                    (1048576u32, 390usize),
                    (268435456u32, 391usize),
                    (1744830499u32, 394usize),
                    (1048576u32, 410usize),
                    (268435456u32, 413usize),
                    (1744830499u32, 415usize),
                    (1048576u32, 598usize),
                    (268435456u32, 599usize),
                    (2012217345u32, 600usize),
                    (2004877313u32, 601usize),
                    (1744830499u32, 602usize),
                    (268435454u32, 603usize),
                    (268435454u32, 612usize),
                    (1048576u32, 379usize),
                    (536870912u32, 380usize),
                    (2012217345u32, 608usize),
                    (2004877313u32, 609usize),
                    (268435454u32, 606usize),
                    (1048576u32, 275usize),
                    (1048576u32, 388usize),
                    (268435456u32, 389usize),
                    (1048576u32, 394usize),
                    (1744830499u32, 397usize),
                    (1048576u32, 411usize),
                    (268435456u32, 412usize),
                    (1048576u32, 415usize),
                    (1744830499u32, 417usize),
                    (1048576u32, 596usize),
                    (268435456u32, 597usize),
                    (1048576u32, 602usize),
                    (2012217345u32, 603usize),
                    (2004877313u32, 604usize),
                    (1744830499u32, 605usize),
                    (268435454u32, 600usize),
                    (268435454u32, 613usize),
                    (268435454u32, 599usize),
                    (16777216u32, 74usize),
                    (1996488705u32, 614usize),
                    (268435454u32, 616usize),
                    (268435454u32, 597usize),
                    (16777216u32, 75usize),
                    (1996488705u32, 615usize),
                    (268435454u32, 617usize),
                    (268435454u32, 598usize),
                    (268435454u32, 614usize),
                    (2013200385u32, 74usize),
                    (65536u32, 253usize),
                    (65536u32, 269usize),
                    (65536u32, 322usize),
                    (65536u32, 324usize),
                    (65536u32, 338usize),
                    (65536u32, 340usize),
                    (65536u32, 378usize),
                    (33554432u32, 381usize),
                    (1744830467u32, 463usize),
                    (8388608u32, 483usize),
                    (65536u32, 484usize),
                    (1744830467u32, 487usize),
                    (1744830467u32, 593usize),
                    (8388608u32, 611usize),
                    (65536u32, 612usize),
                    (16777216u32, 141usize),
                    (1996488705u32, 617usize),
                    (268435454u32, 596usize),
                    (268435454u32, 615usize),
                    (2013265920u32, 74usize),
                    (2013200385u32, 75usize),
                    (1u32, 253usize),
                    (65536u32, 255usize),
                    (1u32, 269usize),
                    (65536u32, 271usize),
                    (1u32, 322usize),
                    (65536u32, 323usize),
                    (1u32, 324usize),
                    (65536u32, 325usize),
                    (1u32, 338usize),
                    (65536u32, 339usize),
                    (1u32, 340usize),
                    (65536u32, 341usize),
                    (1u32, 378usize),
                    (65536u32, 379usize),
                    (33554432u32, 380usize),
                    (512u32, 381usize),
                    (1744830467u32, 465usize),
                    (8388608u32, 482usize),
                    (128u32, 483usize),
                    (1u32, 484usize),
                    (65536u32, 485usize),
                    (1744830467u32, 489usize),
                    (1744830467u32, 595usize),
                    (8388608u32, 610usize),
                    (128u32, 611usize),
                    (1u32, 612usize),
                    (65536u32, 613usize),
                    (16777216u32, 140usize),
                    (1996488705u32, 616usize),
                    (268435454u32, 611usize),
                    (33554432u32, 110usize),
                    (1979711489u32, 618usize),
                    (268435454u32, 620usize),
                    (268435454u32, 610usize),
                    (33554432u32, 111usize),
                    (1979711489u32, 619usize),
                    (268435454u32, 621usize),
                    (268435454u32, 612usize),
                    (268435454u32, 618usize),
                    (2013200385u32, 110usize),
                    (65536u32, 140usize),
                    (65536u32, 274usize),
                    (65536u32, 390usize),
                    (16777216u32, 391usize),
                    (1744830467u32, 394usize),
                    (65536u32, 410usize),
                    (16777216u32, 413usize),
                    (1744830467u32, 415usize),
                    (65536u32, 598usize),
                    (16777216u32, 599usize),
                    (1744830467u32, 602usize),
                    (8388608u32, 81usize),
                    (2004877313u32, 621usize),
                    (268435454u32, 613usize),
                    (268435454u32, 619usize),
                    (2013265920u32, 110usize),
                    (2013200385u32, 111usize),
                    (1u32, 140usize),
                    (65536u32, 141usize),
                    (1u32, 274usize),
                    (65536u32, 275usize),
                    (65536u32, 388usize),
                    (16777216u32, 389usize),
                    (1u32, 390usize),
                    (256u32, 391usize),
                    (1744830467u32, 397usize),
                    (1u32, 410usize),
                    (65536u32, 411usize),
                    (16777216u32, 412usize),
                    (256u32, 413usize),
                    (1744830467u32, 417usize),
                    (65536u32, 596usize),
                    (16777216u32, 597usize),
                    (1u32, 598usize),
                    (256u32, 599usize),
                    (1744830467u32, 605usize),
                    (8388608u32, 80usize),
                    (2004877313u32, 620usize),
                    (268435454u32, 622usize),
                    (268435454u32, 588usize),
                    (268435454u32, 623usize),
                    (33554432u32, 240usize),
                    (1979711489u32, 622usize),
                    (33554432u32, 104usize),
                    (1979711489u32, 588usize),
                    (268435454u32, 624usize),
                    (268435454u32, 623usize),
                    (268435454u32, 524usize),
                    (1879048466u32, 625usize),
                    (268435454u32, 626usize),
                    (268435454u32, 624usize),
                    (33554432u32, 56usize),
                    (1979711489u32, 524usize),
                    (268435454u32, 625usize),
                    (268435454u32, 627usize),
                    (268435454u32, 628usize),
                    (268435454u32, 589usize),
                    (268435454u32, 629usize),
                    (33554432u32, 242usize),
                    (1979711489u32, 628usize),
                    (33554432u32, 105usize),
                    (1979711489u32, 589usize),
                    (268435454u32, 630usize),
                    (268435454u32, 629usize),
                    (268435454u32, 525usize),
                    (1879048466u32, 631usize),
                    (268435454u32, 632usize),
                    (268435454u32, 630usize),
                    (33554432u32, 57usize),
                    (1979711489u32, 525usize),
                    (268435454u32, 631usize),
                    (268435454u32, 633usize),
                    (268435454u32, 634usize),
                    (268435454u32, 618usize),
                    (268435454u32, 635usize),
                    (33554432u32, 244usize),
                    (1979711489u32, 634usize),
                    (33554432u32, 110usize),
                    (1979711489u32, 618usize),
                    (268435454u32, 636usize),
                    (268435454u32, 635usize),
                    (268435454u32, 554usize),
                    (1879048466u32, 637usize),
                    (268435454u32, 638usize),
                    (268435454u32, 636usize),
                    (33554432u32, 62usize),
                    (1979711489u32, 554usize),
                    (268435454u32, 637usize),
                    (268435454u32, 639usize),
                    (268435454u32, 640usize),
                    (268435454u32, 619usize),
                    (268435454u32, 641usize),
                    (33554432u32, 246usize),
                    (1979711489u32, 640usize),
                    (33554432u32, 111usize),
                    (1979711489u32, 619usize),
                    (268435454u32, 642usize),
                    (268435454u32, 641usize),
                    (268435454u32, 555usize),
                    (1879048466u32, 643usize),
                    (268435454u32, 644usize),
                    (268435454u32, 642usize),
                    (33554432u32, 63usize),
                    (1979711489u32, 555usize),
                    (268435454u32, 643usize),
                    (268435454u32, 645usize),
                    (268435454u32, 646usize),
                    (268435454u32, 528usize),
                    (268435454u32, 647usize),
                    (33554432u32, 248usize),
                    (1979711489u32, 646usize),
                    (33554432u32, 116usize),
                    (1979711489u32, 528usize),
                    (268435454u32, 648usize),
                    (268435454u32, 647usize),
                    (268435454u32, 584usize),
                    (1879048466u32, 649usize),
                    (268435454u32, 650usize),
                    (268435454u32, 648usize),
                    (33554432u32, 68usize),
                    (1979711489u32, 584usize),
                    (268435454u32, 649usize),
                    (268435454u32, 651usize),
                    (268435454u32, 652usize),
                    (268435454u32, 529usize),
                    (268435454u32, 653usize),
                    (33554432u32, 250usize),
                    (1979711489u32, 652usize),
                    (33554432u32, 117usize),
                    (1979711489u32, 529usize),
                    (268435454u32, 654usize),
                    (268435454u32, 653usize),
                    (268435454u32, 585usize),
                    (1879048466u32, 655usize),
                    (268435454u32, 656usize),
                    (268435454u32, 654usize),
                    (33554432u32, 69usize),
                    (1979711489u32, 585usize),
                    (268435454u32, 655usize),
                    (268435454u32, 657usize),
                    (268435454u32, 658usize),
                    (268435454u32, 558usize),
                    (268435454u32, 659usize),
                    (33554432u32, 252usize),
                    (1979711489u32, 658usize),
                    (33554432u32, 122usize),
                    (1979711489u32, 558usize),
                    (268435454u32, 660usize),
                    (268435454u32, 659usize),
                    (268435454u32, 614usize),
                    (1879048466u32, 661usize),
                    (268435454u32, 662usize),
                    (268435454u32, 660usize),
                    (33554432u32, 74usize),
                    (1979711489u32, 614usize),
                    (268435454u32, 661usize),
                    (268435454u32, 663usize),
                    (268435454u32, 664usize),
                    (268435454u32, 559usize),
                    (268435454u32, 665usize),
                    (33554432u32, 254usize),
                    (1979711489u32, 664usize),
                    (33554432u32, 123usize),
                    (1979711489u32, 559usize),
                    (268435454u32, 666usize),
                    (268435454u32, 665usize),
                    (268435454u32, 615usize),
                    (1879048466u32, 667usize),
                    (268435454u32, 668usize),
                    (268435454u32, 666usize),
                    (33554432u32, 75usize),
                    (1979711489u32, 615usize),
                    (268435454u32, 667usize),
                    (268435454u32, 669usize),
                    (268435454u32, 620usize),
                    (268435454u32, 670usize),
                    (268435454u32, 671usize),
                    (8388608u32, 80usize),
                    (2004877313u32, 620usize),
                    (8388608u32, 256usize),
                    (2004877313u32, 670usize),
                    (268435454u32, 672usize),
                    (268435454u32, 556usize),
                    (268435454u32, 671usize),
                    (1744831011u32, 673usize),
                    (268435454u32, 674usize),
                    (16777216u32, 128usize),
                    (1996488705u32, 556usize),
                    (536870908u32, 672usize),
                    (268435454u32, 673usize),
                    (268435454u32, 675usize),
                    (268435454u32, 621usize),
                    (268435454u32, 676usize),
                    (268435454u32, 677usize),
                    (8388608u32, 81usize),
                    (2004877313u32, 621usize),
                    (8388608u32, 258usize),
                    (2004877313u32, 676usize),
                    (268435454u32, 678usize),
                    (268435454u32, 557usize),
                    (268435454u32, 677usize),
                    (1744831011u32, 679usize),
                    (268435454u32, 680usize),
                    (16777216u32, 129usize),
                    (1996488705u32, 557usize),
                    (536870908u32, 678usize),
                    (268435454u32, 679usize),
                    (268435454u32, 681usize),
                    (268435454u32, 530usize),
                    (268435454u32, 682usize),
                    (268435454u32, 683usize),
                    (8388608u32, 86usize),
                    (2004877313u32, 530usize),
                    (8388608u32, 260usize),
                    (2004877313u32, 682usize),
                    (268435454u32, 684usize),
                    (268435454u32, 586usize),
                    (268435454u32, 683usize),
                    (1744831011u32, 685usize),
                    (268435454u32, 686usize),
                    (16777216u32, 134usize),
                    (1996488705u32, 586usize),
                    (536870908u32, 684usize),
                    (268435454u32, 685usize),
                    (268435454u32, 687usize),
                    (268435454u32, 531usize),
                    (268435454u32, 688usize),
                    (268435454u32, 689usize),
                    (8388608u32, 87usize),
                    (2004877313u32, 531usize),
                    (8388608u32, 262usize),
                    (2004877313u32, 688usize),
                    (268435454u32, 690usize),
                    (268435454u32, 587usize),
                    (268435454u32, 689usize),
                    (1744831011u32, 691usize),
                    (268435454u32, 692usize),
                    (16777216u32, 135usize),
                    (1996488705u32, 587usize),
                    (536870908u32, 690usize),
                    (268435454u32, 691usize),
                    (268435454u32, 693usize),
                    (268435454u32, 560usize),
                    (268435454u32, 694usize),
                    (268435454u32, 695usize),
                    (8388608u32, 92usize),
                    (2004877313u32, 560usize),
                    (8388608u32, 264usize),
                    (2004877313u32, 694usize),
                    (268435454u32, 696usize),
                    (268435454u32, 616usize),
                    (268435454u32, 695usize),
                    (1744831011u32, 697usize),
                    (268435454u32, 698usize),
                    (16777216u32, 140usize),
                    (1996488705u32, 616usize),
                    (536870908u32, 696usize),
                    (268435454u32, 697usize),
                    (268435454u32, 699usize),
                    (268435454u32, 561usize),
                    (268435454u32, 700usize),
                    (268435454u32, 701usize),
                    (8388608u32, 93usize),
                    (2004877313u32, 561usize),
                    (8388608u32, 266usize),
                    (2004877313u32, 700usize),
                    (268435454u32, 702usize),
                    (268435454u32, 617usize),
                    (268435454u32, 701usize),
                    (1744831011u32, 703usize),
                    (268435454u32, 704usize),
                    (16777216u32, 141usize),
                    (1996488705u32, 617usize),
                    (536870908u32, 702usize),
                    (268435454u32, 703usize),
                    (268435454u32, 705usize),
                    (268435454u32, 590usize),
                    (268435454u32, 706usize),
                    (268435454u32, 707usize),
                    (8388608u32, 98usize),
                    (2004877313u32, 590usize),
                    (8388608u32, 268usize),
                    (2004877313u32, 706usize),
                    (268435454u32, 708usize),
                    (268435454u32, 526usize),
                    (268435454u32, 707usize),
                    (1744831011u32, 709usize),
                    (268435454u32, 710usize),
                    (16777216u32, 146usize),
                    (1996488705u32, 526usize),
                    (536870908u32, 708usize),
                    (268435454u32, 709usize),
                    (268435454u32, 711usize),
                    (268435454u32, 591usize),
                    (268435454u32, 712usize),
                    (268435454u32, 713usize),
                    (8388608u32, 99usize),
                    (2004877313u32, 591usize),
                    (8388608u32, 270usize),
                    (2004877313u32, 712usize),
                    (268435454u32, 714usize),
                    (268435454u32, 527usize),
                    (268435454u32, 713usize),
                    (1744831011u32, 715usize),
                    (268435454u32, 716usize),
                ];
                let mut _vl = 0;
                while _vl < 191usize {
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
                const VS_DESCS: [(usize, usize, usize); 1usize] = [(949usize, 0usize, 6usize)];
                const VS_DEPS: [usize; 6usize] =
                    [764usize, 765usize, 766usize, 767usize, 768usize, 769usize];
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
                let cached = *state.prev_claims.get_unchecked(772usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 1usize));
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(4usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(5usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(6usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(7usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(773usize);
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
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
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
                let cached = *state.prev_claims.get_unchecked(774usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 3usize));
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
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
                let cached = *state.prev_claims.get_unchecked(775usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
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
                let cached = *state.prev_claims.get_unchecked(776usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(16usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(17usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(18usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(19usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(777usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(14usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(15usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(778usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(20usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(21usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(779usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1207959527u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(22usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(23usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(24usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(25usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(780usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(268435422u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(28usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(29usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(30usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(31usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(781usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1207959527u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(26usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(27usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(782usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(268435422u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
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
                let cached = *state.prev_claims.get_unchecked(783usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1342177238u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(34usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(35usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(36usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(37usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(784usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(402653133u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(40usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(41usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(42usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(43usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(785usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1342177238u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
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
                let cached = *state.prev_claims.get_unchecked(786usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(402653133u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(44usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(45usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(787usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1476394949u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(46usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(47usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(48usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(49usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(788usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(536870844u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(52usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(53usize);
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
                let cached = *state.prev_claims.get_unchecked(789usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1476394949u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(50usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(51usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(790usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(536870844u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(56usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(57usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(791usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1610612660u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(58usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(59usize);
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
                let cached = *state.prev_claims.get_unchecked(792usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(671088555u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(64usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(65usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(66usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(67usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(793usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1610612660u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(62usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(63usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(794usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(671088555u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(68usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(69usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(795usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1744830371u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(70usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(71usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(72usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(73usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(796usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(805306266u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(76usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(77usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(78usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(79usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(797usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1744830371u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(74usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(75usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(798usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(805306266u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
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
                let cached = *state.prev_claims.get_unchecked(799usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1879048082u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
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
                let cached = *state.prev_claims.get_unchecked(800usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(939523977u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
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
                let cached = *state.prev_claims.get_unchecked(801usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1879048082u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
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
                let cached = *state.prev_claims.get_unchecked(802usize);
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(939523977u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(92usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(93usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(803usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 32usize));
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(2013265793u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(94usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(95usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(96usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(97usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(804usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 33usize));
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1073741688u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(100usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(101usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(102usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(103usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(805usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 34usize));
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(2013265793u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(98usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(99usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(806usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 35usize));
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1073741688u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(104usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(105usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(807usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 36usize));
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(134217583u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(106usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(107usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(108usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(109usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(808usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 37usize));
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1207959399u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(112usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(113usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(114usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(115usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(809usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 38usize));
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(134217583u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(110usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(111usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(810usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 39usize));
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1207959399u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(116usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(117usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(811usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 40usize));
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(268435294u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(118usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(119usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(120usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(121usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(812usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 41usize));
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1342177110u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(124usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(125usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(126usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(127usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(813usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 42usize));
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(268435294u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(122usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(123usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(814usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 43usize));
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1342177110u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(128usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(129usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(815usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 44usize));
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(402653005u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(130usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(131usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(132usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(133usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(816usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 45usize));
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1476394821u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(136usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(137usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(138usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(139usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(817usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 46usize));
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(402653005u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(134usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(135usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(818usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 47usize));
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1476394821u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(140usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(141usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(819usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 48usize));
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(536870716u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(142usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(143usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(144usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(145usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(820usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 49usize));
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
                    let mut ts_low = *state.prev_claims.get_unchecked(148usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(149usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(150usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(821usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 50usize));
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
                    let mut low = *state.prev_claims.get_unchecked(2usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(536870716u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(3usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(146usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(147usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(822usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 51usize));
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
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(150usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(823usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 52usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(152usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(153usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(154usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(155usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(824usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 53usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(156usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(157usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(158usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(159usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(825usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 54usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(0u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(154usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(155usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(826usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 55usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1073741816u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(158usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(159usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(827usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 56usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(160usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(161usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(162usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(163usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(828usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 57usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1207959527u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(164usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(165usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(166usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(167usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(829usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 58usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(134217711u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(162usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(163usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(830usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 59usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1207959527u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(166usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(167usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(831usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 60usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(268435422u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(168usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(169usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(170usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(171usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(832usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 61usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1342177238u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(172usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(173usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(174usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(175usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(833usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 62usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(268435422u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(170usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(171usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(834usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 63usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1342177238u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(174usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(175usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(835usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 64usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(402653133u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(176usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(177usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(178usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(179usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(836usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 65usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1476394949u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(180usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(181usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(182usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(183usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(837usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 66usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(402653133u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(178usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(179usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(838usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 67usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1476394949u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(182usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(183usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(839usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 68usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(536870844u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(184usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(185usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(186usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(187usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(840usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 69usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1610612660u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(188usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(189usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(190usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(191usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(841usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 70usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(536870844u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(186usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(187usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(842usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 71usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1610612660u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(190usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(191usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(843usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 72usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(671088555u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(192usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(193usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(194usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(195usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(844usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 73usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1744830371u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(196usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(197usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(198usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(199usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(845usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 74usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(671088555u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(194usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(195usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(846usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 75usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1744830371u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(198usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(199usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(847usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 76usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(805306266u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(200usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(201usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(202usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(203usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(848usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 77usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1879048082u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(204usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(205usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(206usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(207usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(849usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 78usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(805306266u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(202usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(203usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(850usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 79usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(1879048082u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(206usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(207usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(851usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 80usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(939523977u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(208usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(209usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(210usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(211usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(852usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 81usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(2013265793u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(212usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(213usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(214usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(215usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(853usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 82usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(939523977u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(210usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(211usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(854usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 83usize));
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
                    let mut low = *state.prev_claims.get_unchecked(150usize);
                    field_ops::add_assign_base(
                        &mut low,
                        &BabyBearField::from_reduced_raw_repr(2013265793u32),
                    );
                    field_ops::mul_assign(&mut t_low, &low);
                    field_ops::add_assign(&mut expected, &t_low);
                }
                {
                    let mut t_high: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[1usize];
                    let high = *state.prev_claims.get_unchecked(151usize);
                    field_ops::mul_assign(&mut t_high, &high);
                    field_ops::add_assign(&mut expected, &t_high);
                }
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(214usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(215usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(855usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 84usize));
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
                    &BabyBearField::from_reduced_raw_repr(1207959527u32),
                );
                field_ops::add_assign(&mut expected, &t_addr);
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(216usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(217usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(218usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(219usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(856usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 85usize));
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
                    &BabyBearField::from_reduced_raw_repr(939519849u32),
                );
                field_ops::add_assign(&mut expected, &t_addr);
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                let cached = *state.prev_claims.get_unchecked(857usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 86usize));
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
                    &BabyBearField::from_reduced_raw_repr(1207959527u32),
                );
                field_ops::add_assign(&mut expected, &t_addr);
                {
                    let mut t_ts: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[2usize];
                    let mut ts_low = *state.prev_claims.get_unchecked(223usize);
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
                    let ts_high = *state.prev_claims.get_unchecked(224usize);
                    field_ops::mul_assign(&mut t_ts, &ts_high);
                    field_ops::add_assign(&mut expected, &t_ts);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[4usize];
                    let val_claim = *state.prev_claims.get_unchecked(220usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                {
                    let mut t_val: BabyBearExt4 =
                        external_challenges.permutation_argument_linearization_challenges[5usize];
                    let val_claim = *state.prev_claims.get_unchecked(221usize);
                    field_ops::mul_assign(&mut t_val, &val_claim);
                    field_ops::add_assign(&mut expected, &t_val);
                }
                let cached = *state.prev_claims.get_unchecked(858usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 87usize));
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
                    &BabyBearField::from_reduced_raw_repr(939519849u32),
                );
                field_ops::add_assign(&mut expected, &t_addr);
                let cached = *state.prev_claims.get_unchecked(859usize);
                if expected != cached {
                    return Err(E::gkr_permutation_cache_relation_failed(0usize, 88usize));
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
