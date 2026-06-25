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
    output_claims: &[BabyBearExt4; 343usize],
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 194usize] = [
            (SimpleGateType::Copy, [626usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::Product,
                [630usize, 631usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [632usize, 633usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [634usize, 635usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [636usize, 637usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [638usize, 639usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [640usize, 641usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [642usize, 643usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [644usize, 645usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [646usize, 647usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [648usize, 649usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [650usize, 651usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [652usize, 653usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [654usize, 655usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [656usize, 657usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [658usize, 659usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [660usize, 661usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [662usize, 663usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [664usize, 665usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [666usize, 667usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [668usize, 669usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [670usize, 671usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [672usize, 673usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [674usize, 675usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [676usize, 677usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [678usize, 679usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [680usize, 681usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [682usize, 683usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [684usize, 685usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [686usize, 687usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [688usize, 689usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [690usize, 691usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [692usize, 693usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [694usize, 695usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [696usize, 697usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [698usize, 699usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [700usize, 701usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [702usize, 703usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [704usize, 705usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [706usize, 707usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [708usize, 709usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [710usize, 711usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [712usize, 713usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [714usize, 715usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::Product,
                [716usize, 717usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupWithSetup,
                [627usize, 493usize, 629usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [628usize, 718usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [719usize, 720usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [721usize, 722usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [723usize, 724usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [725usize, 726usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [727usize, 728usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [729usize, 730usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [731usize, 732usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [733usize, 734usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [735usize, 736usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [737usize, 738usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [739usize, 740usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [741usize, 742usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [743usize, 744usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [745usize, 746usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [747usize, 748usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [749usize, 750usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [751usize, 752usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [753usize, 754usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [755usize, 756usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [757usize, 758usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [759usize, 760usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [761usize, 762usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [763usize, 764usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [765usize, 766usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [767usize, 768usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [769usize, 770usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [771usize, 772usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [773usize, 774usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [775usize, 776usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [777usize, 778usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [779usize, 780usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [781usize, 782usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [783usize, 784usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [785usize, 786usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [787usize, 788usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [789usize, 790usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [791usize, 792usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [793usize, 794usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [795usize, 796usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [797usize, 798usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [799usize, 800usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [801usize, 802usize, 0usize, 0usize],
            ),
            (SimpleGateType::Copy, [803usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupWithSetup,
                [804usize, 494usize, 805usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [806usize, 807usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [808usize, 809usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [810usize, 811usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [812usize, 813usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [814usize, 815usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [816usize, 817usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [818usize, 819usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [820usize, 821usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [822usize, 823usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [824usize, 825usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [826usize, 827usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [828usize, 829usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [830usize, 831usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [832usize, 833usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [834usize, 835usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [836usize, 837usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [838usize, 839usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [840usize, 841usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [842usize, 843usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [844usize, 845usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [846usize, 847usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [848usize, 849usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [850usize, 851usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [852usize, 853usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [854usize, 855usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [856usize, 857usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [858usize, 859usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [860usize, 861usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [862usize, 863usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [864usize, 865usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [866usize, 867usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [868usize, 869usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [870usize, 871usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [872usize, 873usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [874usize, 875usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [876usize, 877usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [878usize, 879usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [880usize, 881usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [882usize, 883usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [884usize, 885usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [886usize, 887usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [888usize, 889usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [890usize, 891usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [892usize, 893usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [894usize, 895usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [896usize, 897usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [898usize, 899usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [900usize, 901usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [902usize, 903usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [904usize, 905usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [906usize, 907usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [908usize, 909usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [910usize, 911usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [912usize, 913usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [914usize, 915usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [916usize, 917usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [918usize, 919usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [920usize, 921usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [922usize, 923usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [924usize, 925usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [926usize, 927usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [928usize, 929usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [930usize, 931usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [932usize, 933usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [934usize, 935usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [936usize, 937usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [938usize, 939usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [940usize, 941usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [942usize, 943usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [944usize, 945usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [946usize, 947usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [948usize, 949usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [950usize, 951usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [952usize, 953usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [954usize, 955usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [956usize, 957usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [958usize, 959usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [960usize, 961usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [962usize, 963usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [964usize, 965usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [966usize, 967usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [968usize, 969usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [970usize, 971usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [972usize, 973usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [974usize, 975usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [976usize, 977usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [978usize, 979usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [980usize, 981usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [982usize, 983usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [984usize, 985usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [986usize, 987usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [988usize, 989usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [990usize, 991usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [992usize, 993usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [994usize, 995usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [996usize, 997usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [998usize, 999usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [1000usize, 1001usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [1002usize, 1003usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [1004usize, 1005usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [1006usize, 1007usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [1008usize, 1009usize, 0usize, 0usize],
            ),
            (
                SimpleGateType::LookupInitialPair,
                [1010usize, 1011usize, 0usize, 0usize],
            ),
        ];
        let mut _sg = 0;
        while _sg < 194usize {
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
            const VAL_COLS: [(usize, usize); 4usize] = [
                (1073741816usize, 0usize),
                (0usize, 1usize),
                (0usize, 2usize),
                (0usize, 1usize),
            ];
            const VAL_VL_TERMS: [(usize, usize); 4usize] = [
                (449usize, 268435454usize),
                (445usize, 536870908usize),
                (447usize, 268435454usize),
                (271usize, 268435454usize),
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(626usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(626usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(626usize, 1744830467usize)];
            let val =
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
                (623usize, 1744830467usize),
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
        for j in 0..2 {
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(2usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(495usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 268309694usize),
                (15usize, 1744830467usize),
                (495usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(15usize, 268435454usize), (527usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(16usize, 1744830467usize), (527usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(496usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 671030187usize),
                (17usize, 1744830467usize),
                (496usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(17usize, 268435454usize), (528usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(18usize, 1744830467usize), (528usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(499usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1878952882usize),
                (19usize, 1744830467usize),
                (499usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(19usize, 268435454usize), (531usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(20usize, 1744830467usize), (531usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(500usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1342074934usize),
                (21usize, 1744830467usize),
                (500usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(21usize, 268435454usize), (532usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(22usize, 1744830467usize), (532usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(503usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1207826599usize),
                (23usize, 1744830467usize),
                (503usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(23usize, 268435454usize), (535usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(24usize, 1744830467usize), (535usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(504usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1342144278usize),
                (25usize, 1744830467usize),
                (504usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(25usize, 268435454usize), (536usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(26usize, 1744830467usize), (536usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(507usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 805172442usize),
                (27usize, 1744830467usize),
                (507usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(27usize, 268435454usize), (539usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(28usize, 1744830467usize), (539usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(508usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1073651544usize),
                (29usize, 1744830467usize),
                (508usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(29usize, 268435454usize), (540usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(30usize, 1744830467usize), (540usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(511usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1744785411usize),
                (31usize, 1744830467usize),
                (511usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(31usize, 268435454usize), (543usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(32usize, 1744830467usize), (543usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(512usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1342133014usize),
                (33usize, 1744830467usize),
                (512usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(33usize, 268435454usize), (544usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(34usize, 1744830467usize), (544usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(515usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1073684728usize),
                (35usize, 1744830467usize),
                (515usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(35usize, 268435454usize), (547usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(36usize, 1744830467usize), (547usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(516usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 671003979usize),
                (37usize, 1744830467usize),
                (516usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(37usize, 268435454usize), (548usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(38usize, 1744830467usize), (548usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(519usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1476276133usize),
                (39usize, 1744830467usize),
                (519usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(39usize, 268435454usize), (551usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(40usize, 1744830467usize), (551usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(520usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1207942343usize),
                (41usize, 1744830467usize),
                (520usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(41usize, 268435454usize), (552usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(42usize, 1744830467usize), (552usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(523usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 1342065270usize),
                (43usize, 1744830467usize),
                (523usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(43usize, 268435454usize), (555usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(44usize, 1744830467usize), (555usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(524usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (2usize, 2013215745usize),
                (45usize, 1744830467usize),
                (524usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 2usize)];
            const VAL_QI: [(usize, usize); 2usize] =
                [(45usize, 268435454usize), (556usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 2usize] =
                [(46usize, 1744830467usize), (556usize, 268435454usize)];
            let val =
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
            const VAL_QI: [(usize, usize); 1usize] = [(559usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 805180538usize),
                (47usize, 1744830467usize),
                (559usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(560usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 671030731usize),
                (48usize, 1744830467usize),
                (560usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(563usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1878952882usize),
                (49usize, 1744830467usize),
                (563usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(564usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1342074934usize),
                (50usize, 1744830467usize),
                (564usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(567usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1207826599usize),
                (51usize, 1744830467usize),
                (567usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(568usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1342144278usize),
                (52usize, 1744830467usize),
                (568usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(571usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 805172442usize),
                (53usize, 1744830467usize),
                (571usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(572usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1073651544usize),
                (54usize, 1744830467usize),
                (572usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(579usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1073684728usize),
                (55usize, 1744830467usize),
                (579usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(580usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 671003979usize),
                (56usize, 1744830467usize),
                (580usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(587usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 1342065270usize),
                (57usize, 1744830467usize),
                (587usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(3usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(588usize, 1744830467usize)];
            const VAL_LN: [(usize, usize); 3usize] = [
                (3usize, 2013215745usize),
                (58usize, 1744830467usize),
                (588usize, 268435454usize),
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (3usize, 1usize), (14usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (3usize, 671043723usize),
                (575usize, 1744830467usize),
                (575usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(59usize, 1744830467usize), (575usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (3usize, 1usize), (14usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (3usize, 1342133014usize),
                (576usize, 1744830467usize),
                (576usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(60usize, 1744830467usize), (576usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (3usize, 1usize), (14usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (3usize, 536849980usize),
                (583usize, 1744830467usize),
                (583usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(61usize, 1744830467usize), (583usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (3usize, 1usize), (14usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (3usize, 805183770usize),
                (584usize, 1744830467usize),
                (584usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(62usize, 1744830467usize), (584usize, 268435454usize)];
            let val =
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
        for j in 0..2 {
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (591usize, 1744830467usize),
                (591usize, 268435454usize),
                (495usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(65usize, 1744830467usize), (591usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (592usize, 1744830467usize),
                (592usize, 268435454usize),
                (496usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(66usize, 1744830467usize), (592usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (593usize, 1744830467usize),
                (593usize, 268435454usize),
                (499usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(67usize, 1744830467usize), (593usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (594usize, 1744830467usize),
                (594usize, 268435454usize),
                (500usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(68usize, 1744830467usize), (594usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (595usize, 1744830467usize),
                (595usize, 268435454usize),
                (503usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(69usize, 1744830467usize), (595usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (596usize, 1744830467usize),
                (596usize, 268435454usize),
                (504usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(70usize, 1744830467usize), (596usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (597usize, 1744830467usize),
                (597usize, 268435454usize),
                (507usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(71usize, 1744830467usize), (597usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (598usize, 1744830467usize),
                (598usize, 268435454usize),
                (508usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(72usize, 1744830467usize), (598usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (599usize, 1744830467usize),
                (599usize, 268435454usize),
                (511usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(73usize, 1744830467usize), (599usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (600usize, 1744830467usize),
                (600usize, 268435454usize),
                (512usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(74usize, 1744830467usize), (600usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (601usize, 1744830467usize),
                (601usize, 268435454usize),
                (515usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(75usize, 1744830467usize), (601usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (602usize, 1744830467usize),
                (602usize, 268435454usize),
                (516usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(76usize, 1744830467usize), (602usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (603usize, 1744830467usize),
                (603usize, 268435454usize),
                (519usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(77usize, 1744830467usize), (603usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (604usize, 1744830467usize),
                (604usize, 268435454usize),
                (520usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(78usize, 1744830467usize), (604usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (605usize, 1744830467usize),
                (605usize, 268435454usize),
                (523usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(79usize, 1744830467usize), (605usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (606usize, 1744830467usize),
                (606usize, 268435454usize),
                (524usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(80usize, 1744830467usize), (606usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (607usize, 1744830467usize),
                (495usize, 268435454usize),
                (591usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(81usize, 1744830467usize), (607usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (608usize, 1744830467usize),
                (496usize, 268435454usize),
                (592usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(82usize, 1744830467usize), (608usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (609usize, 1744830467usize),
                (499usize, 268435454usize),
                (593usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(83usize, 1744830467usize), (609usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (610usize, 1744830467usize),
                (500usize, 268435454usize),
                (594usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(84usize, 1744830467usize), (610usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (611usize, 1744830467usize),
                (503usize, 268435454usize),
                (595usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(85usize, 1744830467usize), (611usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (612usize, 1744830467usize),
                (504usize, 268435454usize),
                (596usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(86usize, 1744830467usize), (612usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (613usize, 1744830467usize),
                (507usize, 268435454usize),
                (597usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(87usize, 1744830467usize), (613usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (614usize, 1744830467usize),
                (508usize, 268435454usize),
                (598usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(88usize, 1744830467usize), (614usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (615usize, 1744830467usize),
                (511usize, 268435454usize),
                (599usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(89usize, 1744830467usize), (615usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (616usize, 1744830467usize),
                (512usize, 268435454usize),
                (600usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(90usize, 1744830467usize), (616usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (617usize, 1744830467usize),
                (515usize, 268435454usize),
                (601usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(91usize, 1744830467usize), (617usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (618usize, 1744830467usize),
                (516usize, 268435454usize),
                (602usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(92usize, 1744830467usize), (618usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (619usize, 1744830467usize),
                (519usize, 268435454usize),
                (603usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(93usize, 1744830467usize), (619usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (620usize, 1744830467usize),
                (520usize, 268435454usize),
                (604usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(94usize, 1744830467usize), (620usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (621usize, 1744830467usize),
                (523usize, 268435454usize),
                (605usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(95usize, 1744830467usize), (621usize, 268435454usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 3usize] =
                [(2usize, 1usize), (63usize, 1usize), (64usize, 1usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (622usize, 1744830467usize),
                (524usize, 268435454usize),
                (606usize, 268435454usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(96usize, 1744830467usize), (622usize, 268435454usize)];
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            let val =
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
            const VAL_LN: [(usize, usize); 1usize] = [(624usize, 268435454usize)];
            let val =
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
                (625usize, 1744830467usize),
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
                (141usize, 268435454usize),
                (142usize, 268435422usize),
                (143usize, 134217455usize),
                (145usize, 1744970275usize),
                (146usize, 1476674629usize),
                (186usize, 268435454usize),
                (187usize, 536869820usize),
                (249usize, 1744970275usize),
                (250usize, 1476674629usize),
                (261usize, 268435454usize),
                (262usize, 268435422usize),
                (263usize, 134217455usize),
                (265usize, 1744970275usize),
                (266usize, 1476674629usize),
                (529usize, 1744830467usize),
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
                (139usize, 268435422usize),
                (140usize, 134217455usize),
                (144usize, 268435454usize),
                (145usize, 268435454usize),
                (146usize, 536870908usize),
                (147usize, 1744970275usize),
                (148usize, 1476674629usize),
                (185usize, 536869820usize),
                (188usize, 268435454usize),
                (249usize, 268435454usize),
                (250usize, 536870908usize),
                (251usize, 1744970275usize),
                (252usize, 1476674629usize),
                (259usize, 268435422usize),
                (260usize, 134217455usize),
                (264usize, 268435454usize),
                (265usize, 268435454usize),
                (266usize, 536870908usize),
                (267usize, 1744970275usize),
                (268usize, 1476674629usize),
                (530usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 23usize] = [
                (20usize, 268435454usize),
                (36usize, 268435454usize),
                (101usize, 268435454usize),
                (103usize, 268435454usize),
                (117usize, 268435454usize),
                (119usize, 268435454usize),
                (159usize, 1744970275usize),
                (160usize, 1476674629usize),
                (171usize, 268435454usize),
                (172usize, 268435422usize),
                (173usize, 134217455usize),
                (175usize, 1744970275usize),
                (176usize, 1476674629usize),
                (216usize, 268435454usize),
                (217usize, 536869820usize),
                (281usize, 1744970275usize),
                (282usize, 1476674629usize),
                (293usize, 268435454usize),
                (294usize, 268435422usize),
                (295usize, 134217455usize),
                (297usize, 1744970275usize),
                (298usize, 1476674629usize),
                (533usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 31usize] = [
                (22usize, 268435454usize),
                (38usize, 268435454usize),
                (102usize, 268435454usize),
                (104usize, 268435454usize),
                (118usize, 268435454usize),
                (120usize, 268435454usize),
                (159usize, 268435454usize),
                (160usize, 536870908usize),
                (161usize, 1744970275usize),
                (162usize, 1476674629usize),
                (169usize, 268435422usize),
                (170usize, 134217455usize),
                (174usize, 268435454usize),
                (175usize, 268435454usize),
                (176usize, 536870908usize),
                (177usize, 1744970275usize),
                (178usize, 1476674629usize),
                (215usize, 536869820usize),
                (218usize, 268435454usize),
                (281usize, 268435454usize),
                (282usize, 536870908usize),
                (283usize, 1744970275usize),
                (284usize, 1476674629usize),
                (291usize, 268435422usize),
                (292usize, 134217455usize),
                (296usize, 268435454usize),
                (297usize, 268435454usize),
                (298usize, 536870908usize),
                (299usize, 1744970275usize),
                (300usize, 1476674629usize),
                (534usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 23usize] = [
                (24usize, 268435454usize),
                (40usize, 268435454usize),
                (105usize, 268435454usize),
                (107usize, 268435454usize),
                (121usize, 268435454usize),
                (123usize, 268435454usize),
                (189usize, 1744970275usize),
                (190usize, 1476674629usize),
                (201usize, 268435454usize),
                (202usize, 268435422usize),
                (203usize, 134217455usize),
                (205usize, 1744970275usize),
                (206usize, 1476674629usize),
                (246usize, 268435454usize),
                (247usize, 536869820usize),
                (313usize, 1744970275usize),
                (314usize, 1476674629usize),
                (325usize, 268435454usize),
                (326usize, 268435422usize),
                (327usize, 134217455usize),
                (329usize, 1744970275usize),
                (330usize, 1476674629usize),
                (537usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 31usize] = [
                (26usize, 268435454usize),
                (42usize, 268435454usize),
                (106usize, 268435454usize),
                (108usize, 268435454usize),
                (122usize, 268435454usize),
                (124usize, 268435454usize),
                (189usize, 268435454usize),
                (190usize, 536870908usize),
                (191usize, 1744970275usize),
                (192usize, 1476674629usize),
                (199usize, 268435422usize),
                (200usize, 134217455usize),
                (204usize, 268435454usize),
                (205usize, 268435454usize),
                (206usize, 536870908usize),
                (207usize, 1744970275usize),
                (208usize, 1476674629usize),
                (245usize, 536869820usize),
                (248usize, 268435454usize),
                (313usize, 268435454usize),
                (314usize, 536870908usize),
                (315usize, 1744970275usize),
                (316usize, 1476674629usize),
                (323usize, 268435422usize),
                (324usize, 134217455usize),
                (328usize, 268435454usize),
                (329usize, 268435454usize),
                (330usize, 536870908usize),
                (331usize, 1744970275usize),
                (332usize, 1476674629usize),
                (538usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 23usize] = [
                (28usize, 268435454usize),
                (44usize, 268435454usize),
                (109usize, 268435454usize),
                (111usize, 268435454usize),
                (125usize, 268435454usize),
                (127usize, 268435454usize),
                (156usize, 268435454usize),
                (157usize, 536869820usize),
                (219usize, 1744970275usize),
                (220usize, 1476674629usize),
                (231usize, 268435454usize),
                (232usize, 268435422usize),
                (233usize, 134217455usize),
                (235usize, 1744970275usize),
                (236usize, 1476674629usize),
                (345usize, 1744970275usize),
                (346usize, 1476674629usize),
                (357usize, 268435454usize),
                (358usize, 268435422usize),
                (359usize, 134217455usize),
                (361usize, 1744970275usize),
                (362usize, 1476674629usize),
                (541usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 31usize] = [
                (30usize, 268435454usize),
                (46usize, 268435454usize),
                (110usize, 268435454usize),
                (112usize, 268435454usize),
                (126usize, 268435454usize),
                (128usize, 268435454usize),
                (155usize, 536869820usize),
                (158usize, 268435454usize),
                (219usize, 268435454usize),
                (220usize, 536870908usize),
                (221usize, 1744970275usize),
                (222usize, 1476674629usize),
                (229usize, 268435422usize),
                (230usize, 134217455usize),
                (234usize, 268435454usize),
                (235usize, 268435454usize),
                (236usize, 536870908usize),
                (237usize, 1744970275usize),
                (238usize, 1476674629usize),
                (345usize, 268435454usize),
                (346usize, 536870908usize),
                (347usize, 1744970275usize),
                (348usize, 1476674629usize),
                (355usize, 268435422usize),
                (356usize, 134217455usize),
                (360usize, 268435454usize),
                (361usize, 268435454usize),
                (362usize, 536870908usize),
                (363usize, 1744970275usize),
                (364usize, 1476674629usize),
                (542usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (374usize, 268435454usize),
                (375usize, 536869820usize),
                (545usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (373usize, 536869820usize),
                (376usize, 268435454usize),
                (546usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (278usize, 268435454usize),
                (279usize, 536869820usize),
                (549usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (277usize, 536869820usize),
                (280usize, 268435454usize),
                (550usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (310usize, 268435454usize),
                (311usize, 536869820usize),
                (553usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (309usize, 536869820usize),
                (312usize, 268435454usize),
                (554usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (342usize, 268435454usize),
                (343usize, 536869820usize),
                (557usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (341usize, 536869820usize),
                (344usize, 268435454usize),
                (558usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 14usize] = [
                (47usize, 268435454usize),
                (135usize, 268435454usize),
                (136usize, 268434910usize),
                (137usize, 1744970275usize),
                (150usize, 268435454usize),
                (151usize, 268434910usize),
                (153usize, 1744970275usize),
                (319usize, 268435454usize),
                (320usize, 268434910usize),
                (321usize, 1744970275usize),
                (336usize, 268435454usize),
                (337usize, 268434910usize),
                (339usize, 1744970275usize),
                (561usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 18usize] = [
                (48usize, 268435454usize),
                (133usize, 268435454usize),
                (134usize, 268434910usize),
                (137usize, 268435454usize),
                (138usize, 1744970275usize),
                (149usize, 268434910usize),
                (152usize, 268435454usize),
                (153usize, 268435454usize),
                (154usize, 1744970275usize),
                (317usize, 268435454usize),
                (318usize, 268434910usize),
                (321usize, 268435454usize),
                (322usize, 1744970275usize),
                (335usize, 268434910usize),
                (338usize, 268435454usize),
                (339usize, 268435454usize),
                (340usize, 1744970275usize),
                (562usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 14usize] = [
                (49usize, 268435454usize),
                (165usize, 268435454usize),
                (166usize, 268434910usize),
                (167usize, 1744970275usize),
                (180usize, 268435454usize),
                (181usize, 268434910usize),
                (183usize, 1744970275usize),
                (351usize, 268435454usize),
                (352usize, 268434910usize),
                (353usize, 1744970275usize),
                (368usize, 268435454usize),
                (369usize, 268434910usize),
                (371usize, 1744970275usize),
                (565usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 18usize] = [
                (50usize, 268435454usize),
                (163usize, 268435454usize),
                (164usize, 268434910usize),
                (167usize, 268435454usize),
                (168usize, 1744970275usize),
                (179usize, 268434910usize),
                (182usize, 268435454usize),
                (183usize, 268435454usize),
                (184usize, 1744970275usize),
                (349usize, 268435454usize),
                (350usize, 268434910usize),
                (353usize, 268435454usize),
                (354usize, 1744970275usize),
                (367usize, 268434910usize),
                (370usize, 268435454usize),
                (371usize, 268435454usize),
                (372usize, 1744970275usize),
                (566usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 14usize] = [
                (51usize, 268435454usize),
                (195usize, 268435454usize),
                (196usize, 268434910usize),
                (197usize, 1744970275usize),
                (210usize, 268435454usize),
                (211usize, 268434910usize),
                (213usize, 1744970275usize),
                (255usize, 268435454usize),
                (256usize, 268434910usize),
                (257usize, 1744970275usize),
                (272usize, 268435454usize),
                (273usize, 268434910usize),
                (275usize, 1744970275usize),
                (569usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 18usize] = [
                (52usize, 268435454usize),
                (193usize, 268435454usize),
                (194usize, 268434910usize),
                (197usize, 268435454usize),
                (198usize, 1744970275usize),
                (209usize, 268434910usize),
                (212usize, 268435454usize),
                (213usize, 268435454usize),
                (214usize, 1744970275usize),
                (253usize, 268435454usize),
                (254usize, 268434910usize),
                (257usize, 268435454usize),
                (258usize, 1744970275usize),
                (271usize, 268434910usize),
                (274usize, 268435454usize),
                (275usize, 268435454usize),
                (276usize, 1744970275usize),
                (570usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 14usize] = [
                (53usize, 268435454usize),
                (225usize, 268435454usize),
                (226usize, 268434910usize),
                (227usize, 1744970275usize),
                (240usize, 268435454usize),
                (241usize, 268434910usize),
                (243usize, 1744970275usize),
                (287usize, 268435454usize),
                (288usize, 268434910usize),
                (289usize, 1744970275usize),
                (304usize, 268435454usize),
                (305usize, 268434910usize),
                (307usize, 1744970275usize),
                (573usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 18usize] = [
                (54usize, 268435454usize),
                (223usize, 268435454usize),
                (224usize, 268434910usize),
                (227usize, 268435454usize),
                (228usize, 1744970275usize),
                (239usize, 268434910usize),
                (242usize, 268435454usize),
                (243usize, 268435454usize),
                (244usize, 1744970275usize),
                (285usize, 268435454usize),
                (286usize, 268434910usize),
                (289usize, 268435454usize),
                (290usize, 1744970275usize),
                (303usize, 268434910usize),
                (306usize, 268435454usize),
                (307usize, 268435454usize),
                (308usize, 1744970275usize),
                (574usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (304usize, 268435454usize),
                (305usize, 268434910usize),
                (577usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (303usize, 268434910usize),
                (306usize, 268435454usize),
                (578usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (336usize, 268435454usize),
                (337usize, 268434910usize),
                (581usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (335usize, 268434910usize),
                (338usize, 268435454usize),
                (582usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (368usize, 268435454usize),
                (369usize, 268434910usize),
                (585usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (367usize, 268434910usize),
                (370usize, 268435454usize),
                (586usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (272usize, 268435454usize),
                (273usize, 268434910usize),
                (589usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (271usize, 268434910usize),
                (274usize, 268435454usize),
                (590usize, 1744830467usize),
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
            const VAL_QO: [(usize, usize); 0usize] = [];
            const VAL_QI: [(usize, usize); 0usize] = [];
            const VAL_LN: [(usize, usize); 3usize] = [
                (269usize, 268435454usize),
                (377usize, 1744830467usize),
                (378usize, 1879048466usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (379usize, 268435454usize),
                (380usize, 134217455usize),
                (495usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(495usize, 268435454usize), (497usize, 1744830467usize)];
            let val =
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (270usize, 268435454usize),
                (381usize, 1744830467usize),
                (382usize, 1879048466usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (383usize, 268435454usize),
                (384usize, 134217455usize),
                (496usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(496usize, 268435454usize), (498usize, 1744830467usize)];
            let val =
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (301usize, 268435454usize),
                (385usize, 1744830467usize),
                (386usize, 1879048466usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (387usize, 268435454usize),
                (388usize, 134217455usize),
                (499usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(499usize, 268435454usize), (501usize, 1744830467usize)];
            let val =
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (302usize, 268435454usize),
                (389usize, 1744830467usize),
                (390usize, 1879048466usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (391usize, 268435454usize),
                (392usize, 134217455usize),
                (500usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(500usize, 268435454usize), (502usize, 1744830467usize)];
            let val =
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (333usize, 268435454usize),
                (393usize, 1744830467usize),
                (394usize, 1879048466usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (395usize, 268435454usize),
                (396usize, 134217455usize),
                (503usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(503usize, 268435454usize), (505usize, 1744830467usize)];
            let val =
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (334usize, 268435454usize),
                (397usize, 1744830467usize),
                (398usize, 1879048466usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (399usize, 268435454usize),
                (400usize, 134217455usize),
                (504usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(504usize, 268435454usize), (506usize, 1744830467usize)];
            let val =
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (365usize, 268435454usize),
                (401usize, 1744830467usize),
                (402usize, 1879048466usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (403usize, 268435454usize),
                (404usize, 134217455usize),
                (507usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(507usize, 268435454usize), (509usize, 1744830467usize)];
            let val =
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (366usize, 268435454usize),
                (405usize, 1744830467usize),
                (406usize, 1879048466usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (407usize, 268435454usize),
                (408usize, 134217455usize),
                (508usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(508usize, 268435454usize), (510usize, 1744830467usize)];
            let val =
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (409usize, 268435454usize),
                (410usize, 1744830467usize),
                (411usize, 1744831011usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (412usize, 268435454usize),
                (413usize, 268434910usize),
                (511usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(511usize, 268435454usize), (513usize, 1744830467usize)];
            let val =
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (414usize, 268435454usize),
                (415usize, 1744830467usize),
                (416usize, 1744831011usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (417usize, 268435454usize),
                (418usize, 268434910usize),
                (512usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(512usize, 268435454usize), (514usize, 1744830467usize)];
            let val =
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (419usize, 268435454usize),
                (420usize, 1744830467usize),
                (421usize, 1744831011usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (422usize, 268435454usize),
                (423usize, 268434910usize),
                (515usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(515usize, 268435454usize), (517usize, 1744830467usize)];
            let val =
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (424usize, 268435454usize),
                (425usize, 1744830467usize),
                (426usize, 1744831011usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (427usize, 268435454usize),
                (428usize, 268434910usize),
                (516usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(516usize, 268435454usize), (518usize, 1744830467usize)];
            let val =
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (429usize, 268435454usize),
                (430usize, 1744830467usize),
                (431usize, 1744831011usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (432usize, 268435454usize),
                (433usize, 268434910usize),
                (519usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(519usize, 268435454usize), (521usize, 1744830467usize)];
            let val =
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (434usize, 268435454usize),
                (435usize, 1744830467usize),
                (436usize, 1744831011usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (437usize, 268435454usize),
                (438usize, 268434910usize),
                (520usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(520usize, 268435454usize), (522usize, 1744830467usize)];
            let val =
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (439usize, 268435454usize),
                (440usize, 1744830467usize),
                (441usize, 1744831011usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (442usize, 268435454usize),
                (443usize, 268434910usize),
                (523usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(523usize, 268435454usize), (525usize, 1744830467usize)];
            let val =
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
            const VAL_LN: [(usize, usize); 3usize] = [
                (444usize, 268435454usize),
                (446usize, 1744830467usize),
                (447usize, 1744831011usize),
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
            const VAL_QO: [(usize, usize); 1usize] = [(13usize, 3usize)];
            const VAL_QI: [(usize, usize); 3usize] = [
                (448usize, 268435454usize),
                (449usize, 268434910usize),
                (524usize, 1744830467usize),
            ];
            const VAL_LN: [(usize, usize); 2usize] =
                [(524usize, 268435454usize), (526usize, 1744830467usize)];
            let val =
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(176usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(176usize, 268435454usize)];
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(177usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(177usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(177usize, 1744830467usize)];
            let val =
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(183usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(183usize, 268435454usize)];
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
        for j in 0..2 {
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(189usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(189usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(189usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(190usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(190usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(190usize, 1744830467usize)];
            let val =
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
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
        for j in 0..2 {
            const VAL_QO: [(usize, usize); 1usize] = [(235usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(235usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(235usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(236usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(236usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(236usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(237usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(237usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(237usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(238usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(238usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(238usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(243usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(243usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(243usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(244usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(244usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(244usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(249usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(249usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(249usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(250usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(250usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(250usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(251usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(251usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(251usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(252usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(252usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(252usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(257usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(257usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(257usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(258usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(258usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(258usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(265usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(265usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(265usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(266usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(266usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(266usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(267usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(267usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(267usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(268usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(268usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(268usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(275usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(275usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(275usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(276usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(276usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(276usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(281usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(281usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(281usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(282usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(282usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(282usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(283usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(283usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(283usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(284usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(284usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(284usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(289usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(289usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(289usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(290usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(290usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(290usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(297usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(297usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(297usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(298usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(298usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(298usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(299usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(299usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(299usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(300usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(300usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(300usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(307usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(307usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(307usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(308usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(308usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(308usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(313usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(313usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(313usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(314usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(314usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(314usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(315usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(315usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(315usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(316usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(316usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(316usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(321usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(321usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(321usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(322usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(322usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(322usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(329usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(329usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(329usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(330usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(330usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(330usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(331usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(331usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(331usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(332usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(332usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(332usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(339usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(339usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(339usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(340usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(340usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(340usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(345usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(345usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(345usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(346usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(346usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(346usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(347usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(347usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(347usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(348usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(348usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(348usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(353usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(353usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(353usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(354usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(354usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(354usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(361usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(361usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(361usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(362usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(362usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(362usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(363usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(363usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(363usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(364usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(364usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(364usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(371usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(371usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(371usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(372usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(372usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(372usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(378usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(378usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(378usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(382usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(382usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(382usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(386usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(386usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(386usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(390usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(390usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(390usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(394usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(394usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(394usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(398usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(398usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(398usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(402usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(402usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(402usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(406usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(406usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(406usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(411usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(411usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(411usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(416usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(416usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(416usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(421usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(421usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(421usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(426usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(426usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(426usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(431usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(431usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(431usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(436usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(436usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(436usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(441usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(441usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(441usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(447usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(447usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(447usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(450usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(450usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(450usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(451usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(451usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(451usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(452usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(452usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(452usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(453usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(453usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(453usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(454usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(454usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(454usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(455usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(455usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(455usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(456usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(456usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(456usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(457usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(457usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(457usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(458usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(458usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(458usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(459usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(459usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(459usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(460usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(460usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(460usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(461usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(461usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(461usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(462usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(462usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(462usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(463usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(463usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(463usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(464usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(464usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(464usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(465usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(465usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(465usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(466usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(466usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(466usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(467usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(467usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(467usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(468usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(468usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(468usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(469usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(469usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(469usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(470usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(470usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(470usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(471usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(471usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(471usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(472usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(472usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(472usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(473usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(473usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(473usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(474usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(474usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(474usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(475usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(475usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(475usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(476usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(476usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(476usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(477usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(477usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(477usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(478usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(478usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(478usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(479usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(479usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(479usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(480usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(480usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(480usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(481usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(481usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(481usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(482usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(482usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(482usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(483usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(483usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(483usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(484usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(484usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(484usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(485usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(485usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(485usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(486usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(486usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(486usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(487usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(487usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(487usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(488usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(488usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(488usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(489usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(489usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(489usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(490usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(490usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(490usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(491usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(491usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(491usize, 1744830467usize)];
            let val =
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
            const VAL_QO: [(usize, usize); 1usize] = [(492usize, 1usize)];
            const VAL_QI: [(usize, usize); 1usize] = [(492usize, 268435454usize)];
            const VAL_LN: [(usize, usize); 1usize] = [(492usize, 1744830467usize)];
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
    output_claims: &[BabyBearExt4; 175usize],
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 101usize] = [
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
                [131usize, 132usize, 133usize, 0usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [129usize, 130usize, 127usize, 128usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [125usize, 126usize, 123usize, 124usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [121usize, 122usize, 119usize, 120usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [117usize, 118usize, 115usize, 116usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [113usize, 114usize, 111usize, 112usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [109usize, 110usize, 107usize, 108usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [105usize, 106usize, 103usize, 104usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [101usize, 102usize, 99usize, 100usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [97usize, 98usize, 95usize, 96usize],
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
            (SimpleGateType::Copy, [45usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [46usize, 0usize, 0usize, 0usize]),
            (
                SimpleGateType::LookupUnbalanced,
                [340usize, 341usize, 342usize, 0usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [338usize, 339usize, 336usize, 337usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [334usize, 335usize, 332usize, 333usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [330usize, 331usize, 328usize, 329usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [326usize, 327usize, 324usize, 325usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [322usize, 323usize, 320usize, 321usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [318usize, 319usize, 316usize, 317usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [314usize, 315usize, 312usize, 313usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [310usize, 311usize, 308usize, 309usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [306usize, 307usize, 304usize, 305usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [302usize, 303usize, 300usize, 301usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [298usize, 299usize, 296usize, 297usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [294usize, 295usize, 292usize, 293usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [290usize, 291usize, 288usize, 289usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [286usize, 287usize, 284usize, 285usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [282usize, 283usize, 280usize, 281usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [278usize, 279usize, 276usize, 277usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [274usize, 275usize, 272usize, 273usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [270usize, 271usize, 268usize, 269usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [266usize, 267usize, 264usize, 265usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [262usize, 263usize, 260usize, 261usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [258usize, 259usize, 256usize, 257usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [254usize, 255usize, 252usize, 253usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [250usize, 251usize, 248usize, 249usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [246usize, 247usize, 244usize, 245usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [242usize, 243usize, 240usize, 241usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [238usize, 239usize, 236usize, 237usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [234usize, 235usize, 232usize, 233usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [230usize, 231usize, 228usize, 229usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [226usize, 227usize, 224usize, 225usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [222usize, 223usize, 220usize, 221usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [218usize, 219usize, 216usize, 217usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [214usize, 215usize, 212usize, 213usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [210usize, 211usize, 208usize, 209usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [206usize, 207usize, 204usize, 205usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [202usize, 203usize, 200usize, 201usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [198usize, 199usize, 196usize, 197usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [194usize, 195usize, 192usize, 193usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [190usize, 191usize, 188usize, 189usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [186usize, 187usize, 184usize, 185usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [182usize, 183usize, 180usize, 181usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [178usize, 179usize, 176usize, 177usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [174usize, 175usize, 172usize, 173usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [170usize, 171usize, 168usize, 169usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [166usize, 167usize, 164usize, 165usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [162usize, 163usize, 160usize, 161usize],
            ),
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
            (SimpleGateType::Copy, [134usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [135usize, 0usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 101usize {
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
    output_claims: &[BabyBearExt4; 91usize],
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
                [67usize, 68usize, 65usize, 66usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [63usize, 64usize, 61usize, 62usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [59usize, 60usize, 57usize, 58usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [55usize, 56usize, 53usize, 54usize],
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
            (SimpleGateType::Copy, [23usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [24usize, 0usize, 0usize, 0usize]),
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
            (
                SimpleGateType::LookupAggregatePair,
                [137usize, 138usize, 135usize, 136usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [133usize, 134usize, 131usize, 132usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [129usize, 130usize, 127usize, 128usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [125usize, 126usize, 123usize, 124usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [121usize, 122usize, 119usize, 120usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [117usize, 118usize, 115usize, 116usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [113usize, 114usize, 111usize, 112usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [109usize, 110usize, 107usize, 108usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [105usize, 106usize, 103usize, 104usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [101usize, 102usize, 99usize, 100usize],
            ),
            (
                SimpleGateType::LookupAggregatePair,
                [97usize, 98usize, 95usize, 96usize],
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
            (SimpleGateType::Copy, [69usize, 0usize, 0usize, 0usize]),
            (SimpleGateType::Copy, [70usize, 0usize, 0usize, 0usize]),
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
    acc
}
#[inline(always)]
#[allow(unused_variables)]
unsafe fn layer_3_compute_claim(
    output_claims: &[BabyBearExt4; 47usize],
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 28usize] = [
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
        ];
        let mut _sg = 0;
        while _sg < 28usize {
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
    output_claims: &[BabyBearExt4; 25usize],
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 15usize] = [
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
        ];
        let mut _sg = 0;
        while _sg < 15usize {
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
    output_claims: &[BabyBearExt4; 15usize],
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
        const SIMPLE_GATES: [(SimpleGateType, [usize; 4]); 11usize] = [
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
        ];
        let mut _sg = 0;
        while _sg < 11usize {
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
unsafe fn layer_6_compute_claim(
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
unsafe fn layer_6_final_step_accumulator(
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
#[allow(unused_variables)]
unsafe fn layer_7_compute_claim(
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
unsafe fn layer_7_final_step_accumulator(
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
        let pt = state.prev_point.get_unchecked(..20usize);
        let mut result: BabyBearExt4 = BabyBearExt4::ZERO;
        let mut prefactor: BabyBearField = BabyBearField::ONE;
        let mut k: usize = 0;
        while k < 19usize {
            let mut t = *pt.get_unchecked(20usize - 1 - k);
            field_ops::mul_assign_by_base(&mut t, &prefactor);
            field_ops::add_assign(&mut result, &t);
            field_ops::double(&mut prefactor);
            k += 1;
        }
        while k < 20usize {
            let mut t: BabyBearExt4 = BabyBearExt4::ONE;
            let p = pt.get_unchecked(20usize - 1 - k);
            field_ops::sub_assign(&mut t, &*p);
            field_ops::mul_assign(&mut result, &t);
            k += 1;
        }
        if result != *state.prev_claims.get_unchecked(875usize) {
            return Err(E::gkr_virtual_setup_eval_mismatch(875usize));
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
                    nd_source,
                )?;
            let mut fc_len = 3usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
                    nd_source,
                )?;
            let mut fc_len = 4usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
                    nd_source,
                )?;
            let mut fc_len = 5usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
                    nd_source,
                )?;
            let mut fc_len = 6usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
                    nd_source,
                )?;
            let mut fc_len = 7usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
                    nd_source,
                )?;
            let mut fc_len = 8usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
                    nd_source,
                )?;
            let mut fc_len = 9usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
                    nd_source,
                )?;
            let mut fc_len = 10usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
                    nd_source,
                )?;
            let mut fc_len = 11usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
                    nd_source,
                )?;
            let mut fc_len = 12usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
                    nd_source,
                )?;
            let mut fc_len = 13usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
                    nd_source,
                )?;
            let mut fc_len = 14usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
                    nd_source,
                )?;
            let mut fc_len = 15usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
                    nd_source,
                )?;
            let mut fc_len = 16usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
                    nd_source,
                )?;
            let mut fc_len = 17usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
                    nd_source,
                )?;
            let mut fc_len = 18usize;
            let data_words = 6usize * 4 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
            let initial_claim = layer_7_compute_claim(
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
                let f = layer_7_final_step_accumulator(
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
                    7usize,
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
            verifier_common::stats::log("GKR MAIN LAYER 7");
        }
        {
            let initial_claim = layer_6_compute_claim(
                state.prev_claims.as_array::<8usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    6usize,
                    nd_source,
                )?;
            let mut fc_len = 19usize;
            let data_words = 15usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
                    &external_challenges.permutation_argument_linearization_challenges,
                    external_challenges.permutation_argument_additive_part,
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
            draw_field_els_into::<DRAW_BUF_CAPACITY>(ts, draw_buf.as_mut_slice());
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
            #[cfg(feature = "verifier_stats")]
            verifier_common::stats::log("GKR MAIN LAYER 6");
        }
        {
            let initial_claim = layer_5_compute_claim(
                state.prev_claims.as_array::<15usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    5usize,
                    nd_source,
                )?;
            let mut fc_len = 19usize;
            let data_words = 25usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
            fold_standard_claims::<25usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<25usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    4usize,
                    nd_source,
                )?;
            let mut fc_len = 19usize;
            let data_words = 47usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
            fold_standard_claims::<47usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<47usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    3usize,
                    nd_source,
                )?;
            let mut fc_len = 19usize;
            let data_words = 91usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
            fold_standard_claims::<91usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<91usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    2usize,
                    nd_source,
                )?;
            let mut fc_len = 19usize;
            let data_words = 175usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
            fold_standard_claims::<175usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<175usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    1usize,
                    nd_source,
                )?;
            let mut fc_len = 19usize;
            let data_words = 343usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
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
            fold_standard_claims::<343usize, GKR_ADDRS, GKR_EVAL_BUF>(
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
                state.prev_claims.as_array::<343usize>(),
                state.batching_challenge,
            );
            let (final_claim, final_eq_prefactor) =
                verify_sumcheck_rounds::<I, E, 19usize, GKR_COMMIT_BUF>(
                    ts,
                    initial_claim,
                    &mut state.prev_point,
                    0usize,
                    nd_source,
                )?;
            let mut fc_len = 19usize;
            let data_words = 1012usize * 2 * EXT_DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 2]] = eval_buf.data_as(1012usize);
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
                let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + 246usize * EXT_DEGREE;
                total.div_ceil(BLAKE2S_BLOCK_SIZE_U32_WORDS) * BLAKE2S_BLOCK_SIZE_U32_WORDS
            };
            let mut extra_buf = CommitBuf::<EXTRA_COMMIT_BUF>::new();
            let extra_data_words = 246usize * EXT_DEGREE;
            {
                let mut i = 0;
                while i < extra_data_words {
                    extra_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                    i += 1;
                }
            }
            let mut extra_evals = LazyVec::<BabyBearExt4, 246usize>::new();
            {
                let slice: &[BabyBearExt4] = unsafe { extra_buf.data_as(246usize) };
                for el in slice {
                    extra_evals.push(*el);
                }
            }
            ts.commit(&mut extra_buf, extra_data_words);
            let final_step_evals: &[[BabyBearExt4; 2]] = unsafe { eval_buf.data_as(1012usize) };
            state.prev_claims.clear();
            {
                const LAYOUT_KIND: [usize; 1258usize] = [
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize,
                    1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize,
                    0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize,
                    1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize,
                    0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize,
                    1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize,
                    0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize,
                    1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize,
                    0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize,
                    1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize,
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
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize,
                    1usize, 0usize, 0usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 0usize, 0usize, 1usize,
                    0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    1usize, 1usize, 1usize, 0usize, 0usize, 1usize, 0usize, 0usize, 0usize, 0usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 1usize,
                    1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 0usize,
                    0usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize,
                    1usize, 1usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 1usize,
                    1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize,
                    0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize,
                    1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize,
                    0usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize,
                    0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize,
                    0usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize,
                    1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 0usize, 0usize,
                    0usize, 0usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize,
                    1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 0usize,
                    0usize, 0usize, 0usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize,
                    1usize, 0usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 0usize, 1usize,
                    0usize, 0usize, 0usize, 0usize, 1usize, 0usize, 1usize, 0usize, 0usize, 0usize,
                    0usize, 1usize, 0usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 0usize,
                    1usize, 0usize, 0usize, 0usize, 0usize, 1usize, 0usize, 1usize, 0usize, 0usize,
                    0usize, 0usize, 1usize, 0usize, 1usize, 0usize, 0usize, 0usize, 0usize, 1usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                    0usize, 1usize, 1usize, 1usize, 1usize, 0usize, 0usize, 0usize, 0usize, 0usize,
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
                    0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize, 0usize,
                ];
                const LAYOUT_POS: [usize; 1258usize] = [
                    151usize, 152usize, 153usize, 154usize, 155usize, 156usize, 495usize, 496usize,
                    497usize, 498usize, 157usize, 158usize, 499usize, 500usize, 501usize, 502usize,
                    159usize, 160usize, 503usize, 504usize, 505usize, 506usize, 161usize, 162usize,
                    507usize, 508usize, 509usize, 510usize, 163usize, 164usize, 511usize, 512usize,
                    513usize, 514usize, 165usize, 166usize, 515usize, 516usize, 517usize, 518usize,
                    167usize, 168usize, 519usize, 520usize, 521usize, 522usize, 169usize, 170usize,
                    523usize, 524usize, 525usize, 526usize, 171usize, 172usize, 527usize, 528usize,
                    529usize, 530usize, 173usize, 174usize, 531usize, 532usize, 533usize, 534usize,
                    175usize, 176usize, 535usize, 536usize, 537usize, 538usize, 177usize, 178usize,
                    539usize, 540usize, 541usize, 542usize, 179usize, 180usize, 543usize, 544usize,
                    545usize, 546usize, 181usize, 182usize, 547usize, 548usize, 549usize, 550usize,
                    183usize, 184usize, 551usize, 552usize, 553usize, 554usize, 185usize, 186usize,
                    555usize, 556usize, 557usize, 558usize, 187usize, 188usize, 559usize, 560usize,
                    561usize, 562usize, 189usize, 190usize, 563usize, 564usize, 565usize, 566usize,
                    191usize, 192usize, 567usize, 568usize, 569usize, 570usize, 193usize, 194usize,
                    571usize, 572usize, 573usize, 574usize, 195usize, 196usize, 575usize, 576usize,
                    577usize, 578usize, 197usize, 198usize, 579usize, 580usize, 581usize, 582usize,
                    199usize, 200usize, 583usize, 584usize, 585usize, 586usize, 201usize, 202usize,
                    587usize, 588usize, 589usize, 590usize, 203usize, 204usize, 205usize, 206usize,
                    207usize, 208usize, 591usize, 592usize, 209usize, 210usize, 593usize, 594usize,
                    211usize, 212usize, 595usize, 596usize, 213usize, 214usize, 597usize, 598usize,
                    215usize, 216usize, 599usize, 600usize, 217usize, 218usize, 601usize, 602usize,
                    219usize, 220usize, 603usize, 604usize, 221usize, 222usize, 605usize, 606usize,
                    223usize, 224usize, 607usize, 608usize, 225usize, 226usize, 609usize, 610usize,
                    227usize, 228usize, 611usize, 612usize, 229usize, 230usize, 613usize, 614usize,
                    231usize, 232usize, 615usize, 616usize, 233usize, 234usize, 617usize, 618usize,
                    235usize, 236usize, 619usize, 620usize, 237usize, 238usize, 621usize, 622usize,
                    239usize, 240usize, 241usize, 623usize, 624usize, 625usize, 626usize, 627usize,
                    628usize, 0usize, 1usize, 2usize, 3usize, 4usize, 5usize, 6usize, 7usize,
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
                    129usize, 130usize, 131usize, 132usize, 0usize, 1usize, 2usize, 133usize,
                    134usize, 3usize, 135usize, 136usize, 137usize, 138usize, 4usize, 5usize,
                    6usize, 7usize, 8usize, 9usize, 139usize, 140usize, 141usize, 10usize, 11usize,
                    142usize, 143usize, 144usize, 145usize, 146usize, 147usize, 148usize, 12usize,
                    13usize, 149usize, 150usize, 151usize, 152usize, 153usize, 154usize, 14usize,
                    15usize, 155usize, 156usize, 157usize, 158usize, 159usize, 160usize, 161usize,
                    162usize, 16usize, 17usize, 18usize, 163usize, 164usize, 19usize, 165usize,
                    166usize, 167usize, 168usize, 20usize, 21usize, 22usize, 23usize, 24usize,
                    25usize, 169usize, 170usize, 171usize, 26usize, 27usize, 172usize, 173usize,
                    174usize, 175usize, 176usize, 177usize, 178usize, 28usize, 29usize, 179usize,
                    180usize, 181usize, 182usize, 183usize, 184usize, 30usize, 31usize, 185usize,
                    186usize, 187usize, 188usize, 189usize, 190usize, 191usize, 192usize, 32usize,
                    33usize, 34usize, 193usize, 194usize, 35usize, 195usize, 196usize, 197usize,
                    198usize, 36usize, 37usize, 38usize, 39usize, 40usize, 41usize, 199usize,
                    200usize, 201usize, 42usize, 43usize, 202usize, 203usize, 204usize, 205usize,
                    206usize, 207usize, 208usize, 44usize, 45usize, 209usize, 210usize, 211usize,
                    212usize, 213usize, 214usize, 46usize, 47usize, 215usize, 216usize, 217usize,
                    218usize, 219usize, 220usize, 221usize, 222usize, 48usize, 49usize, 50usize,
                    223usize, 224usize, 51usize, 225usize, 226usize, 227usize, 228usize, 52usize,
                    53usize, 54usize, 55usize, 56usize, 57usize, 229usize, 230usize, 231usize,
                    58usize, 59usize, 232usize, 233usize, 234usize, 235usize, 236usize, 237usize,
                    238usize, 60usize, 61usize, 239usize, 240usize, 241usize, 242usize, 243usize,
                    244usize, 62usize, 63usize, 245usize, 246usize, 247usize, 248usize, 249usize,
                    250usize, 251usize, 252usize, 64usize, 65usize, 253usize, 254usize, 255usize,
                    256usize, 257usize, 258usize, 66usize, 67usize, 68usize, 69usize, 70usize,
                    71usize, 259usize, 260usize, 261usize, 72usize, 73usize, 262usize, 263usize,
                    264usize, 265usize, 266usize, 267usize, 268usize, 269usize, 270usize, 271usize,
                    272usize, 273usize, 274usize, 275usize, 276usize, 74usize, 75usize, 277usize,
                    278usize, 279usize, 280usize, 281usize, 282usize, 283usize, 284usize, 76usize,
                    77usize, 285usize, 286usize, 287usize, 288usize, 289usize, 290usize, 78usize,
                    79usize, 80usize, 81usize, 82usize, 83usize, 291usize, 292usize, 293usize,
                    84usize, 85usize, 294usize, 295usize, 296usize, 297usize, 298usize, 299usize,
                    300usize, 301usize, 302usize, 303usize, 304usize, 305usize, 306usize, 307usize,
                    308usize, 86usize, 87usize, 309usize, 310usize, 311usize, 312usize, 313usize,
                    314usize, 315usize, 316usize, 88usize, 89usize, 317usize, 318usize, 319usize,
                    320usize, 321usize, 322usize, 90usize, 91usize, 92usize, 93usize, 94usize,
                    95usize, 323usize, 324usize, 325usize, 96usize, 97usize, 326usize, 327usize,
                    328usize, 329usize, 330usize, 331usize, 332usize, 333usize, 334usize, 335usize,
                    336usize, 337usize, 338usize, 339usize, 340usize, 98usize, 99usize, 341usize,
                    342usize, 343usize, 344usize, 345usize, 346usize, 347usize, 348usize, 100usize,
                    101usize, 349usize, 350usize, 351usize, 352usize, 353usize, 354usize, 102usize,
                    103usize, 104usize, 105usize, 106usize, 107usize, 355usize, 356usize, 357usize,
                    108usize, 109usize, 358usize, 359usize, 360usize, 361usize, 362usize, 363usize,
                    364usize, 365usize, 366usize, 367usize, 368usize, 369usize, 370usize, 371usize,
                    372usize, 110usize, 111usize, 373usize, 374usize, 375usize, 376usize, 112usize,
                    113usize, 114usize, 377usize, 378usize, 379usize, 380usize, 115usize, 116usize,
                    117usize, 381usize, 382usize, 383usize, 384usize, 118usize, 119usize, 120usize,
                    385usize, 386usize, 387usize, 388usize, 121usize, 122usize, 123usize, 389usize,
                    390usize, 391usize, 392usize, 124usize, 125usize, 126usize, 393usize, 394usize,
                    395usize, 396usize, 127usize, 128usize, 129usize, 397usize, 398usize, 399usize,
                    400usize, 130usize, 131usize, 132usize, 401usize, 402usize, 403usize, 404usize,
                    133usize, 134usize, 135usize, 405usize, 406usize, 407usize, 408usize, 136usize,
                    409usize, 137usize, 410usize, 411usize, 412usize, 413usize, 138usize, 414usize,
                    139usize, 415usize, 416usize, 417usize, 418usize, 140usize, 419usize, 141usize,
                    420usize, 421usize, 422usize, 423usize, 142usize, 424usize, 143usize, 425usize,
                    426usize, 427usize, 428usize, 144usize, 429usize, 145usize, 430usize, 431usize,
                    432usize, 433usize, 146usize, 434usize, 147usize, 435usize, 436usize, 437usize,
                    438usize, 148usize, 439usize, 149usize, 440usize, 441usize, 442usize, 443usize,
                    150usize, 444usize, 445usize, 446usize, 447usize, 448usize, 449usize, 450usize,
                    451usize, 452usize, 453usize, 454usize, 455usize, 456usize, 457usize, 458usize,
                    459usize, 460usize, 461usize, 462usize, 463usize, 464usize, 465usize, 466usize,
                    467usize, 468usize, 469usize, 470usize, 471usize, 472usize, 473usize, 474usize,
                    475usize, 476usize, 477usize, 478usize, 479usize, 480usize, 481usize, 482usize,
                    483usize, 484usize, 485usize, 486usize, 487usize, 488usize, 489usize, 490usize,
                    491usize, 492usize, 493usize, 494usize, 242usize, 243usize, 244usize, 245usize,
                    629usize, 630usize, 631usize, 632usize, 633usize, 634usize, 635usize, 636usize,
                    637usize, 638usize, 639usize, 640usize, 641usize, 642usize, 643usize, 644usize,
                    645usize, 646usize, 647usize, 648usize, 649usize, 650usize, 651usize, 652usize,
                    653usize, 654usize, 655usize, 656usize, 657usize, 658usize, 659usize, 660usize,
                    661usize, 662usize, 663usize, 664usize, 665usize, 666usize, 667usize, 668usize,
                    669usize, 670usize, 671usize, 672usize, 673usize, 674usize, 675usize, 676usize,
                    677usize, 678usize, 679usize, 680usize, 681usize, 682usize, 683usize, 684usize,
                    685usize, 686usize, 687usize, 688usize, 689usize, 690usize, 691usize, 692usize,
                    693usize, 694usize, 695usize, 696usize, 697usize, 698usize, 699usize, 700usize,
                    701usize, 702usize, 703usize, 704usize, 705usize, 706usize, 707usize, 708usize,
                    709usize, 710usize, 711usize, 712usize, 713usize, 714usize, 715usize, 716usize,
                    717usize, 718usize, 719usize, 720usize, 721usize, 722usize, 723usize, 724usize,
                    725usize, 726usize, 727usize, 728usize, 729usize, 730usize, 731usize, 732usize,
                    733usize, 734usize, 735usize, 736usize, 737usize, 738usize, 739usize, 740usize,
                    741usize, 742usize, 743usize, 744usize, 745usize, 746usize, 747usize, 748usize,
                    749usize, 750usize, 751usize, 752usize, 753usize, 754usize, 755usize, 756usize,
                    757usize, 758usize, 759usize, 760usize, 761usize, 762usize, 763usize, 764usize,
                    765usize, 766usize, 767usize, 768usize, 769usize, 770usize, 771usize, 772usize,
                    773usize, 774usize, 775usize, 776usize, 777usize, 778usize, 779usize, 780usize,
                    781usize, 782usize, 783usize, 784usize, 785usize, 786usize, 787usize, 788usize,
                    789usize, 790usize, 791usize, 792usize, 793usize, 794usize, 795usize, 796usize,
                    797usize, 798usize, 799usize, 800usize, 801usize, 802usize, 803usize, 804usize,
                    805usize, 806usize, 807usize, 808usize, 809usize, 810usize, 811usize, 812usize,
                    813usize, 814usize, 815usize, 816usize, 817usize, 818usize, 819usize, 820usize,
                    821usize, 822usize, 823usize, 824usize, 825usize, 826usize, 827usize, 828usize,
                    829usize, 830usize, 831usize, 832usize, 833usize, 834usize, 835usize, 836usize,
                    837usize, 838usize, 839usize, 840usize, 841usize, 842usize, 843usize, 844usize,
                    845usize, 846usize, 847usize, 848usize, 849usize, 850usize, 851usize, 852usize,
                    853usize, 854usize, 855usize, 856usize, 857usize, 858usize, 859usize, 860usize,
                    861usize, 862usize, 863usize, 864usize, 865usize, 866usize, 867usize, 868usize,
                    869usize, 870usize, 871usize, 872usize, 873usize, 874usize, 875usize, 876usize,
                    877usize, 878usize, 879usize, 880usize, 881usize, 882usize, 883usize, 884usize,
                    885usize, 886usize, 887usize, 888usize, 889usize, 890usize, 891usize, 892usize,
                    893usize, 894usize, 895usize, 896usize, 897usize, 898usize, 899usize, 900usize,
                    901usize, 902usize, 903usize, 904usize, 905usize, 906usize, 907usize, 908usize,
                    909usize, 910usize, 911usize, 912usize, 913usize, 914usize, 915usize, 916usize,
                    917usize, 918usize, 919usize, 920usize, 921usize, 922usize, 923usize, 924usize,
                    925usize, 926usize, 927usize, 928usize, 929usize, 930usize, 931usize, 932usize,
                    933usize, 934usize, 935usize, 936usize, 937usize, 938usize, 939usize, 940usize,
                    941usize, 942usize, 943usize, 944usize, 945usize, 946usize, 947usize, 948usize,
                    949usize, 950usize, 951usize, 952usize, 953usize, 954usize, 955usize, 956usize,
                    957usize, 958usize, 959usize, 960usize, 961usize, 962usize, 963usize, 964usize,
                    965usize, 966usize, 967usize, 968usize, 969usize, 970usize, 971usize, 972usize,
                    973usize, 974usize, 975usize, 976usize, 977usize, 978usize, 979usize, 980usize,
                    981usize, 982usize, 983usize, 984usize, 985usize, 986usize, 987usize, 988usize,
                    989usize, 990usize, 991usize, 992usize, 993usize, 994usize, 995usize, 996usize,
                    997usize, 998usize, 999usize, 1000usize, 1001usize, 1002usize, 1003usize,
                    1004usize, 1005usize, 1006usize, 1007usize, 1008usize, 1009usize, 1010usize,
                    1011usize,
                ];
                let mut i = 0usize;
                while i < 1258usize {
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
                const SC_DESCS: [(usize, u32, usize, usize); 86usize] = [
                    (964usize, 1476395013u32, 0usize, 3usize),
                    (965usize, 133099247u32, 3usize, 3usize),
                    (966usize, 1476395013u32, 6usize, 3usize),
                    (967usize, 133099247u32, 9usize, 3usize),
                    (968usize, 1476395013u32, 12usize, 3usize),
                    (969usize, 133099247u32, 15usize, 3usize),
                    (970usize, 1476395013u32, 18usize, 3usize),
                    (971usize, 133099247u32, 21usize, 3usize),
                    (972usize, 1476395013u32, 24usize, 3usize),
                    (973usize, 133099247u32, 27usize, 3usize),
                    (974usize, 1476395013u32, 30usize, 3usize),
                    (975usize, 133099247u32, 33usize, 3usize),
                    (976usize, 1476395013u32, 36usize, 3usize),
                    (977usize, 133099247u32, 39usize, 3usize),
                    (978usize, 1476395013u32, 42usize, 3usize),
                    (979usize, 133099247u32, 45usize, 3usize),
                    (980usize, 1476395013u32, 48usize, 3usize),
                    (981usize, 133099247u32, 51usize, 3usize),
                    (982usize, 1476395013u32, 54usize, 3usize),
                    (983usize, 133099247u32, 57usize, 3usize),
                    (984usize, 1476395013u32, 60usize, 3usize),
                    (985usize, 133099247u32, 63usize, 3usize),
                    (986usize, 1476395013u32, 66usize, 3usize),
                    (987usize, 133099247u32, 69usize, 3usize),
                    (988usize, 1476395013u32, 72usize, 3usize),
                    (989usize, 133099247u32, 75usize, 3usize),
                    (990usize, 1476395013u32, 78usize, 3usize),
                    (991usize, 133099247u32, 81usize, 3usize),
                    (992usize, 1476395013u32, 84usize, 3usize),
                    (993usize, 133099247u32, 87usize, 3usize),
                    (994usize, 1476395013u32, 90usize, 3usize),
                    (995usize, 133099247u32, 93usize, 3usize),
                    (996usize, 1476395013u32, 96usize, 3usize),
                    (997usize, 133099247u32, 99usize, 3usize),
                    (998usize, 1476395013u32, 102usize, 3usize),
                    (999usize, 133099247u32, 105usize, 3usize),
                    (1000usize, 1476395013u32, 108usize, 3usize),
                    (1001usize, 133099247u32, 111usize, 3usize),
                    (1002usize, 1476395013u32, 114usize, 3usize),
                    (1003usize, 133099247u32, 117usize, 3usize),
                    (1004usize, 1476395013u32, 120usize, 3usize),
                    (1005usize, 133099247u32, 123usize, 3usize),
                    (1006usize, 1476395013u32, 126usize, 3usize),
                    (1007usize, 133099247u32, 129usize, 3usize),
                    (1008usize, 1476395013u32, 132usize, 3usize),
                    (1009usize, 133099247u32, 135usize, 3usize),
                    (1010usize, 1476395013u32, 138usize, 3usize),
                    (1011usize, 133099247u32, 141usize, 3usize),
                    (1012usize, 1476395013u32, 144usize, 3usize),
                    (1013usize, 133099247u32, 147usize, 3usize),
                    (1014usize, 1476395013u32, 150usize, 3usize),
                    (1015usize, 133099247u32, 153usize, 3usize),
                    (1016usize, 1476395013u32, 156usize, 3usize),
                    (1017usize, 133099247u32, 159usize, 3usize),
                    (1018usize, 1476395013u32, 162usize, 3usize),
                    (1019usize, 133099247u32, 165usize, 3usize),
                    (1020usize, 1476395013u32, 168usize, 3usize),
                    (1021usize, 133099247u32, 171usize, 3usize),
                    (1022usize, 1476395013u32, 174usize, 3usize),
                    (1023usize, 133099247u32, 177usize, 3usize),
                    (1024usize, 1476395013u32, 180usize, 3usize),
                    (1025usize, 133099247u32, 183usize, 3usize),
                    (1026usize, 1476395013u32, 186usize, 3usize),
                    (1027usize, 133099247u32, 189usize, 3usize),
                    (1028usize, 1476395013u32, 192usize, 3usize),
                    (1029usize, 133099247u32, 195usize, 3usize),
                    (1030usize, 1476395013u32, 198usize, 3usize),
                    (1031usize, 133099247u32, 201usize, 3usize),
                    (1032usize, 1476395013u32, 204usize, 3usize),
                    (1033usize, 133099247u32, 207usize, 3usize),
                    (1034usize, 1476395013u32, 210usize, 3usize),
                    (1035usize, 133099247u32, 213usize, 3usize),
                    (1036usize, 1476395013u32, 216usize, 3usize),
                    (1037usize, 133099247u32, 219usize, 3usize),
                    (1038usize, 1476395013u32, 222usize, 3usize),
                    (1039usize, 133099247u32, 225usize, 3usize),
                    (1040usize, 1476395013u32, 228usize, 3usize),
                    (1041usize, 133099247u32, 231usize, 3usize),
                    (1042usize, 1476395013u32, 234usize, 3usize),
                    (1043usize, 133099247u32, 237usize, 3usize),
                    (1044usize, 1476395013u32, 240usize, 3usize),
                    (1045usize, 133099247u32, 243usize, 3usize),
                    (1046usize, 1476395013u32, 246usize, 3usize),
                    (1047usize, 133099247u32, 249usize, 3usize),
                    (1048usize, 1476395013u32, 252usize, 3usize),
                    (1049usize, 133099247u32, 255usize, 3usize),
                ];
                const SC_TERMS: [(u32, usize); 258usize] = [
                    (1744830467u32, 223usize),
                    (268435454u32, 0usize),
                    (133099247u32, 826usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 1usize),
                    (1744830467u32, 826usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 4usize),
                    (133099247u32, 827usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 5usize),
                    (1744830467u32, 827usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 10usize),
                    (133099247u32, 828usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 11usize),
                    (1744830467u32, 828usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 16usize),
                    (133099247u32, 829usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 17usize),
                    (1744830467u32, 829usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 22usize),
                    (133099247u32, 830usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 23usize),
                    (1744830467u32, 830usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 28usize),
                    (133099247u32, 831usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 29usize),
                    (1744830467u32, 831usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 34usize),
                    (133099247u32, 832usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 35usize),
                    (1744830467u32, 832usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 40usize),
                    (133099247u32, 833usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 41usize),
                    (1744830467u32, 833usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 46usize),
                    (133099247u32, 834usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 47usize),
                    (1744830467u32, 834usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 52usize),
                    (133099247u32, 835usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 53usize),
                    (1744830467u32, 835usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 58usize),
                    (133099247u32, 836usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 59usize),
                    (1744830467u32, 836usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 64usize),
                    (133099247u32, 837usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 65usize),
                    (1744830467u32, 837usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 70usize),
                    (133099247u32, 838usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 71usize),
                    (1744830467u32, 838usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 76usize),
                    (133099247u32, 839usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 77usize),
                    (1744830467u32, 839usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 82usize),
                    (133099247u32, 840usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 83usize),
                    (1744830467u32, 840usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 88usize),
                    (133099247u32, 841usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 89usize),
                    (1744830467u32, 841usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 94usize),
                    (133099247u32, 842usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 95usize),
                    (1744830467u32, 842usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 100usize),
                    (133099247u32, 843usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 101usize),
                    (1744830467u32, 843usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 106usize),
                    (133099247u32, 844usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 107usize),
                    (1744830467u32, 844usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 112usize),
                    (133099247u32, 845usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 113usize),
                    (1744830467u32, 845usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 118usize),
                    (133099247u32, 846usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 119usize),
                    (1744830467u32, 846usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 124usize),
                    (133099247u32, 847usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 125usize),
                    (1744830467u32, 847usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 130usize),
                    (133099247u32, 848usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 131usize),
                    (1744830467u32, 848usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 136usize),
                    (133099247u32, 849usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 137usize),
                    (1744830467u32, 849usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 142usize),
                    (133099247u32, 850usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 143usize),
                    (1744830467u32, 850usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 148usize),
                    (133099247u32, 851usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 149usize),
                    (1744830467u32, 851usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 152usize),
                    (133099247u32, 852usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 153usize),
                    (1744830467u32, 852usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 156usize),
                    (133099247u32, 853usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 157usize),
                    (1744830467u32, 853usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 160usize),
                    (133099247u32, 854usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 161usize),
                    (1744830467u32, 854usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 164usize),
                    (133099247u32, 855usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 165usize),
                    (1744830467u32, 855usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 168usize),
                    (133099247u32, 856usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 169usize),
                    (1744830467u32, 856usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 172usize),
                    (133099247u32, 857usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 173usize),
                    (1744830467u32, 857usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 176usize),
                    (133099247u32, 858usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 177usize),
                    (1744830467u32, 858usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 180usize),
                    (133099247u32, 859usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 181usize),
                    (1744830467u32, 859usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 184usize),
                    (133099247u32, 860usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 185usize),
                    (1744830467u32, 860usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 188usize),
                    (133099247u32, 861usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 189usize),
                    (1744830467u32, 861usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 192usize),
                    (133099247u32, 862usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 193usize),
                    (1744830467u32, 862usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 196usize),
                    (133099247u32, 863usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 197usize),
                    (1744830467u32, 863usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 200usize),
                    (133099247u32, 864usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 201usize),
                    (1744830467u32, 864usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 204usize),
                    (133099247u32, 865usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 205usize),
                    (1744830467u32, 865usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 208usize),
                    (133099247u32, 866usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 209usize),
                    (1744830467u32, 866usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 212usize),
                    (133099247u32, 867usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 213usize),
                    (1744830467u32, 867usize),
                    (1744830467u32, 223usize),
                    (268435454u32, 216usize),
                    (133099247u32, 868usize),
                    (1744830467u32, 224usize),
                    (268435454u32, 217usize),
                    (1744830467u32, 868usize),
                ];
                let mut _sc = 0;
                while _sc < 86usize {
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
                const VL_DESCS: [(usize, usize, usize); 207usize] = [
                    (1050usize, 0usize, 4usize),
                    (1052usize, 4usize, 4usize),
                    (1053usize, 8usize, 4usize),
                    (1054usize, 12usize, 4usize),
                    (1055usize, 16usize, 4usize),
                    (1056usize, 20usize, 4usize),
                    (1057usize, 24usize, 4usize),
                    (1058usize, 28usize, 4usize),
                    (1059usize, 32usize, 4usize),
                    (1060usize, 36usize, 4usize),
                    (1061usize, 40usize, 4usize),
                    (1062usize, 44usize, 4usize),
                    (1063usize, 48usize, 4usize),
                    (1064usize, 52usize, 4usize),
                    (1065usize, 56usize, 4usize),
                    (1066usize, 60usize, 4usize),
                    (1067usize, 64usize, 4usize),
                    (1068usize, 68usize, 4usize),
                    (1069usize, 72usize, 4usize),
                    (1070usize, 76usize, 4usize),
                    (1071usize, 80usize, 4usize),
                    (1072usize, 84usize, 4usize),
                    (1073usize, 88usize, 4usize),
                    (1074usize, 92usize, 4usize),
                    (1075usize, 96usize, 4usize),
                    (1076usize, 100usize, 4usize),
                    (1077usize, 104usize, 4usize),
                    (1078usize, 108usize, 4usize),
                    (1079usize, 112usize, 4usize),
                    (1080usize, 116usize, 4usize),
                    (1081usize, 120usize, 4usize),
                    (1082usize, 124usize, 4usize),
                    (1083usize, 128usize, 4usize),
                    (1084usize, 132usize, 4usize),
                    (1085usize, 136usize, 4usize),
                    (1086usize, 140usize, 4usize),
                    (1087usize, 144usize, 4usize),
                    (1088usize, 148usize, 4usize),
                    (1089usize, 152usize, 4usize),
                    (1090usize, 156usize, 4usize),
                    (1091usize, 160usize, 4usize),
                    (1092usize, 164usize, 4usize),
                    (1093usize, 168usize, 4usize),
                    (1094usize, 172usize, 4usize),
                    (1095usize, 176usize, 4usize),
                    (1096usize, 180usize, 4usize),
                    (1097usize, 184usize, 4usize),
                    (1098usize, 188usize, 4usize),
                    (1099usize, 192usize, 4usize),
                    (1100usize, 196usize, 4usize),
                    (1101usize, 200usize, 4usize),
                    (1102usize, 204usize, 4usize),
                    (1103usize, 208usize, 4usize),
                    (1104usize, 212usize, 4usize),
                    (1105usize, 216usize, 4usize),
                    (1106usize, 220usize, 4usize),
                    (1107usize, 224usize, 4usize),
                    (1108usize, 228usize, 4usize),
                    (1109usize, 232usize, 4usize),
                    (1110usize, 236usize, 4usize),
                    (1111usize, 240usize, 4usize),
                    (1112usize, 244usize, 4usize),
                    (1113usize, 248usize, 4usize),
                    (1114usize, 252usize, 4usize),
                    (1115usize, 256usize, 4usize),
                    (1116usize, 260usize, 4usize),
                    (1117usize, 264usize, 4usize),
                    (1118usize, 268usize, 4usize),
                    (1119usize, 272usize, 4usize),
                    (1120usize, 276usize, 4usize),
                    (1121usize, 280usize, 4usize),
                    (1122usize, 284usize, 4usize),
                    (1123usize, 288usize, 4usize),
                    (1124usize, 292usize, 4usize),
                    (1125usize, 296usize, 4usize),
                    (1126usize, 300usize, 4usize),
                    (1127usize, 304usize, 4usize),
                    (1128usize, 308usize, 4usize),
                    (1129usize, 312usize, 4usize),
                    (1130usize, 316usize, 4usize),
                    (1131usize, 320usize, 4usize),
                    (1132usize, 324usize, 4usize),
                    (1133usize, 328usize, 4usize),
                    (1134usize, 332usize, 4usize),
                    (1135usize, 336usize, 4usize),
                    (1136usize, 340usize, 4usize),
                    (1137usize, 344usize, 4usize),
                    (1138usize, 348usize, 4usize),
                    (1139usize, 352usize, 4usize),
                    (1140usize, 356usize, 4usize),
                    (1141usize, 360usize, 4usize),
                    (1142usize, 364usize, 4usize),
                    (1143usize, 368usize, 4usize),
                    (1144usize, 372usize, 4usize),
                    (1145usize, 376usize, 4usize),
                    (1146usize, 380usize, 4usize),
                    (1147usize, 384usize, 4usize),
                    (1148usize, 388usize, 4usize),
                    (1149usize, 392usize, 4usize),
                    (1150usize, 396usize, 4usize),
                    (1151usize, 400usize, 4usize),
                    (1152usize, 404usize, 4usize),
                    (1153usize, 408usize, 4usize),
                    (1154usize, 412usize, 4usize),
                    (1155usize, 416usize, 4usize),
                    (1156usize, 420usize, 4usize),
                    (1157usize, 424usize, 4usize),
                    (1158usize, 428usize, 4usize),
                    (1159usize, 432usize, 4usize),
                    (1160usize, 436usize, 4usize),
                    (1161usize, 440usize, 4usize),
                    (1162usize, 444usize, 4usize),
                    (1163usize, 448usize, 4usize),
                    (1164usize, 452usize, 4usize),
                    (1165usize, 456usize, 4usize),
                    (1166usize, 460usize, 4usize),
                    (1167usize, 464usize, 4usize),
                    (1168usize, 468usize, 4usize),
                    (1169usize, 472usize, 4usize),
                    (1170usize, 476usize, 4usize),
                    (1171usize, 480usize, 4usize),
                    (1172usize, 484usize, 4usize),
                    (1173usize, 488usize, 4usize),
                    (1174usize, 492usize, 4usize),
                    (1175usize, 496usize, 4usize),
                    (1176usize, 500usize, 4usize),
                    (1177usize, 504usize, 4usize),
                    (1178usize, 508usize, 4usize),
                    (1179usize, 512usize, 4usize),
                    (1180usize, 516usize, 4usize),
                    (1181usize, 520usize, 4usize),
                    (1182usize, 524usize, 4usize),
                    (1183usize, 528usize, 4usize),
                    (1184usize, 532usize, 4usize),
                    (1185usize, 536usize, 4usize),
                    (1186usize, 540usize, 4usize),
                    (1187usize, 544usize, 4usize),
                    (1188usize, 548usize, 4usize),
                    (1189usize, 552usize, 4usize),
                    (1190usize, 556usize, 4usize),
                    (1191usize, 560usize, 4usize),
                    (1192usize, 564usize, 4usize),
                    (1193usize, 568usize, 4usize),
                    (1194usize, 572usize, 4usize),
                    (1195usize, 576usize, 4usize),
                    (1196usize, 580usize, 4usize),
                    (1197usize, 584usize, 4usize),
                    (1198usize, 588usize, 4usize),
                    (1199usize, 592usize, 4usize),
                    (1200usize, 596usize, 4usize),
                    (1201usize, 600usize, 4usize),
                    (1202usize, 604usize, 4usize),
                    (1203usize, 608usize, 4usize),
                    (1204usize, 612usize, 4usize),
                    (1205usize, 616usize, 4usize),
                    (1206usize, 620usize, 4usize),
                    (1207usize, 624usize, 4usize),
                    (1208usize, 628usize, 4usize),
                    (1209usize, 632usize, 4usize),
                    (1210usize, 636usize, 4usize),
                    (1211usize, 640usize, 4usize),
                    (1212usize, 644usize, 4usize),
                    (1213usize, 648usize, 4usize),
                    (1214usize, 652usize, 4usize),
                    (1215usize, 656usize, 4usize),
                    (1216usize, 660usize, 4usize),
                    (1217usize, 664usize, 4usize),
                    (1218usize, 668usize, 4usize),
                    (1219usize, 672usize, 4usize),
                    (1220usize, 676usize, 4usize),
                    (1221usize, 680usize, 4usize),
                    (1222usize, 684usize, 4usize),
                    (1223usize, 688usize, 4usize),
                    (1224usize, 692usize, 4usize),
                    (1225usize, 696usize, 4usize),
                    (1226usize, 700usize, 4usize),
                    (1227usize, 704usize, 4usize),
                    (1228usize, 708usize, 4usize),
                    (1229usize, 712usize, 4usize),
                    (1230usize, 716usize, 4usize),
                    (1231usize, 720usize, 4usize),
                    (1232usize, 724usize, 4usize),
                    (1233usize, 728usize, 4usize),
                    (1234usize, 732usize, 4usize),
                    (1235usize, 736usize, 4usize),
                    (1236usize, 740usize, 4usize),
                    (1237usize, 744usize, 4usize),
                    (1238usize, 748usize, 4usize),
                    (1239usize, 752usize, 4usize),
                    (1240usize, 756usize, 4usize),
                    (1241usize, 760usize, 4usize),
                    (1242usize, 764usize, 4usize),
                    (1243usize, 768usize, 4usize),
                    (1244usize, 772usize, 4usize),
                    (1245usize, 776usize, 4usize),
                    (1246usize, 780usize, 4usize),
                    (1247usize, 784usize, 4usize),
                    (1248usize, 788usize, 4usize),
                    (1249usize, 792usize, 4usize),
                    (1250usize, 796usize, 4usize),
                    (1251usize, 800usize, 4usize),
                    (1252usize, 804usize, 4usize),
                    (1253usize, 808usize, 4usize),
                    (1254usize, 812usize, 4usize),
                    (1255usize, 816usize, 4usize),
                    (1256usize, 820usize, 4usize),
                    (1257usize, 824usize, 4usize),
                ];
                const VL_COLS: [(u32, usize, usize); 828usize] = [
                    (0u32, 0usize, 1usize),
                    (0u32, 1usize, 1usize),
                    (0u32, 2usize, 1usize),
                    (1073741816u32, 3usize, 0usize),
                    (0u32, 3usize, 2usize),
                    (0u32, 5usize, 6usize),
                    (0u32, 11usize, 1usize),
                    (1073741816u32, 12usize, 0usize),
                    (0u32, 12usize, 1usize),
                    (0u32, 13usize, 1usize),
                    (0u32, 14usize, 1usize),
                    (1073741816u32, 15usize, 0usize),
                    (0u32, 15usize, 2usize),
                    (0u32, 17usize, 8usize),
                    (0u32, 25usize, 1usize),
                    (1073741816u32, 26usize, 0usize),
                    (0u32, 26usize, 1usize),
                    (0u32, 27usize, 1usize),
                    (0u32, 28usize, 1usize),
                    (536870876u32, 29usize, 0usize),
                    (0u32, 29usize, 1usize),
                    (0u32, 30usize, 1usize),
                    (0u32, 31usize, 1usize),
                    (1342177238u32, 32usize, 0usize),
                    (0u32, 32usize, 3usize),
                    (0u32, 35usize, 6usize),
                    (0u32, 41usize, 1usize),
                    (805306330u32, 42usize, 0usize),
                    (0u32, 42usize, 1usize),
                    (0u32, 43usize, 1usize),
                    (0u32, 44usize, 1usize),
                    (536870876u32, 45usize, 0usize),
                    (0u32, 45usize, 1usize),
                    (0u32, 46usize, 1usize),
                    (0u32, 47usize, 1usize),
                    (1342177238u32, 48usize, 0usize),
                    (0u32, 48usize, 3usize),
                    (0u32, 51usize, 7usize),
                    (0u32, 58usize, 1usize),
                    (805306330u32, 59usize, 0usize),
                    (0u32, 59usize, 1usize),
                    (0u32, 60usize, 1usize),
                    (0u32, 61usize, 1usize),
                    (1073741816u32, 62usize, 0usize),
                    (0u32, 62usize, 1usize),
                    (0u32, 63usize, 12usize),
                    (0u32, 75usize, 1usize),
                    (1073741816u32, 76usize, 0usize),
                    (0u32, 76usize, 1usize),
                    (0u32, 77usize, 1usize),
                    (0u32, 78usize, 1usize),
                    (1073741816u32, 79usize, 0usize),
                    (0u32, 79usize, 1usize),
                    (0u32, 80usize, 16usize),
                    (0u32, 96usize, 1usize),
                    (1073741816u32, 97usize, 0usize),
                    (0u32, 97usize, 2usize),
                    (0u32, 99usize, 1usize),
                    (0u32, 100usize, 1usize),
                    (1073741784u32, 101usize, 0usize),
                    (0u32, 101usize, 1usize),
                    (0u32, 102usize, 8usize),
                    (0u32, 110usize, 1usize),
                    (1342177238u32, 111usize, 0usize),
                    (0u32, 111usize, 2usize),
                    (0u32, 113usize, 1usize),
                    (0u32, 114usize, 1usize),
                    (1073741784u32, 115usize, 0usize),
                    (0u32, 115usize, 1usize),
                    (0u32, 116usize, 10usize),
                    (0u32, 126usize, 1usize),
                    (1342177238u32, 127usize, 0usize),
                    (0u32, 127usize, 1usize),
                    (0u32, 128usize, 1usize),
                    (0u32, 129usize, 1usize),
                    (1073741816u32, 130usize, 0usize),
                    (0u32, 130usize, 2usize),
                    (0u32, 132usize, 6usize),
                    (0u32, 138usize, 1usize),
                    (1073741816u32, 139usize, 0usize),
                    (0u32, 139usize, 1usize),
                    (0u32, 140usize, 1usize),
                    (0u32, 141usize, 1usize),
                    (1073741816u32, 142usize, 0usize),
                    (0u32, 142usize, 2usize),
                    (0u32, 144usize, 8usize),
                    (0u32, 152usize, 1usize),
                    (1073741816u32, 153usize, 0usize),
                    (0u32, 153usize, 1usize),
                    (0u32, 154usize, 1usize),
                    (0u32, 155usize, 1usize),
                    (536870876u32, 156usize, 0usize),
                    (0u32, 156usize, 1usize),
                    (0u32, 157usize, 1usize),
                    (0u32, 158usize, 1usize),
                    (1342177238u32, 159usize, 0usize),
                    (0u32, 159usize, 3usize),
                    (0u32, 162usize, 6usize),
                    (0u32, 168usize, 1usize),
                    (805306330u32, 169usize, 0usize),
                    (0u32, 169usize, 1usize),
                    (0u32, 170usize, 1usize),
                    (0u32, 171usize, 1usize),
                    (536870876u32, 172usize, 0usize),
                    (0u32, 172usize, 1usize),
                    (0u32, 173usize, 1usize),
                    (0u32, 174usize, 1usize),
                    (1342177238u32, 175usize, 0usize),
                    (0u32, 175usize, 3usize),
                    (0u32, 178usize, 7usize),
                    (0u32, 185usize, 1usize),
                    (805306330u32, 186usize, 0usize),
                    (0u32, 186usize, 1usize),
                    (0u32, 187usize, 1usize),
                    (0u32, 188usize, 1usize),
                    (1073741816u32, 189usize, 0usize),
                    (0u32, 189usize, 1usize),
                    (0u32, 190usize, 12usize),
                    (0u32, 202usize, 1usize),
                    (1073741816u32, 203usize, 0usize),
                    (0u32, 203usize, 1usize),
                    (0u32, 204usize, 1usize),
                    (0u32, 205usize, 1usize),
                    (1073741816u32, 206usize, 0usize),
                    (0u32, 206usize, 1usize),
                    (0u32, 207usize, 16usize),
                    (0u32, 223usize, 1usize),
                    (1073741816u32, 224usize, 0usize),
                    (0u32, 224usize, 2usize),
                    (0u32, 226usize, 1usize),
                    (0u32, 227usize, 1usize),
                    (1073741784u32, 228usize, 0usize),
                    (0u32, 228usize, 1usize),
                    (0u32, 229usize, 8usize),
                    (0u32, 237usize, 1usize),
                    (1342177238u32, 238usize, 0usize),
                    (0u32, 238usize, 2usize),
                    (0u32, 240usize, 1usize),
                    (0u32, 241usize, 1usize),
                    (1073741784u32, 242usize, 0usize),
                    (0u32, 242usize, 1usize),
                    (0u32, 243usize, 10usize),
                    (0u32, 253usize, 1usize),
                    (1342177238u32, 254usize, 0usize),
                    (0u32, 254usize, 1usize),
                    (0u32, 255usize, 1usize),
                    (0u32, 256usize, 1usize),
                    (1073741816u32, 257usize, 0usize),
                    (0u32, 257usize, 2usize),
                    (0u32, 259usize, 6usize),
                    (0u32, 265usize, 1usize),
                    (1073741816u32, 266usize, 0usize),
                    (0u32, 266usize, 1usize),
                    (0u32, 267usize, 1usize),
                    (0u32, 268usize, 1usize),
                    (1073741816u32, 269usize, 0usize),
                    (0u32, 269usize, 2usize),
                    (0u32, 271usize, 8usize),
                    (0u32, 279usize, 1usize),
                    (1073741816u32, 280usize, 0usize),
                    (0u32, 280usize, 1usize),
                    (0u32, 281usize, 1usize),
                    (0u32, 282usize, 1usize),
                    (536870876u32, 283usize, 0usize),
                    (0u32, 283usize, 1usize),
                    (0u32, 284usize, 1usize),
                    (0u32, 285usize, 1usize),
                    (1342177238u32, 286usize, 0usize),
                    (0u32, 286usize, 3usize),
                    (0u32, 289usize, 6usize),
                    (0u32, 295usize, 1usize),
                    (805306330u32, 296usize, 0usize),
                    (0u32, 296usize, 1usize),
                    (0u32, 297usize, 1usize),
                    (0u32, 298usize, 1usize),
                    (536870876u32, 299usize, 0usize),
                    (0u32, 299usize, 1usize),
                    (0u32, 300usize, 1usize),
                    (0u32, 301usize, 1usize),
                    (1342177238u32, 302usize, 0usize),
                    (0u32, 302usize, 3usize),
                    (0u32, 305usize, 7usize),
                    (0u32, 312usize, 1usize),
                    (805306330u32, 313usize, 0usize),
                    (0u32, 313usize, 1usize),
                    (0u32, 314usize, 1usize),
                    (0u32, 315usize, 1usize),
                    (1073741816u32, 316usize, 0usize),
                    (0u32, 316usize, 1usize),
                    (0u32, 317usize, 12usize),
                    (0u32, 329usize, 1usize),
                    (1073741816u32, 330usize, 0usize),
                    (0u32, 330usize, 1usize),
                    (0u32, 331usize, 1usize),
                    (0u32, 332usize, 1usize),
                    (1073741816u32, 333usize, 0usize),
                    (0u32, 333usize, 1usize),
                    (0u32, 334usize, 16usize),
                    (0u32, 350usize, 1usize),
                    (1073741816u32, 351usize, 0usize),
                    (0u32, 351usize, 2usize),
                    (0u32, 353usize, 1usize),
                    (0u32, 354usize, 1usize),
                    (1073741784u32, 355usize, 0usize),
                    (0u32, 355usize, 1usize),
                    (0u32, 356usize, 8usize),
                    (0u32, 364usize, 1usize),
                    (1342177238u32, 365usize, 0usize),
                    (0u32, 365usize, 2usize),
                    (0u32, 367usize, 1usize),
                    (0u32, 368usize, 1usize),
                    (1073741784u32, 369usize, 0usize),
                    (0u32, 369usize, 1usize),
                    (0u32, 370usize, 10usize),
                    (0u32, 380usize, 1usize),
                    (1342177238u32, 381usize, 0usize),
                    (0u32, 381usize, 1usize),
                    (0u32, 382usize, 1usize),
                    (0u32, 383usize, 1usize),
                    (1073741816u32, 384usize, 0usize),
                    (0u32, 384usize, 2usize),
                    (0u32, 386usize, 6usize),
                    (0u32, 392usize, 1usize),
                    (1073741816u32, 393usize, 0usize),
                    (0u32, 393usize, 1usize),
                    (0u32, 394usize, 1usize),
                    (0u32, 395usize, 1usize),
                    (1073741816u32, 396usize, 0usize),
                    (0u32, 396usize, 2usize),
                    (0u32, 398usize, 8usize),
                    (0u32, 406usize, 1usize),
                    (1073741816u32, 407usize, 0usize),
                    (0u32, 407usize, 1usize),
                    (0u32, 408usize, 1usize),
                    (0u32, 409usize, 1usize),
                    (536870876u32, 410usize, 0usize),
                    (0u32, 410usize, 1usize),
                    (0u32, 411usize, 1usize),
                    (0u32, 412usize, 1usize),
                    (1342177238u32, 413usize, 0usize),
                    (0u32, 413usize, 3usize),
                    (0u32, 416usize, 6usize),
                    (0u32, 422usize, 1usize),
                    (805306330u32, 423usize, 0usize),
                    (0u32, 423usize, 1usize),
                    (0u32, 424usize, 1usize),
                    (0u32, 425usize, 1usize),
                    (536870876u32, 426usize, 0usize),
                    (0u32, 426usize, 1usize),
                    (0u32, 427usize, 1usize),
                    (0u32, 428usize, 1usize),
                    (1342177238u32, 429usize, 0usize),
                    (0u32, 429usize, 3usize),
                    (0u32, 432usize, 7usize),
                    (0u32, 439usize, 1usize),
                    (805306330u32, 440usize, 0usize),
                    (0u32, 440usize, 1usize),
                    (0u32, 441usize, 1usize),
                    (0u32, 442usize, 1usize),
                    (1073741816u32, 443usize, 0usize),
                    (0u32, 443usize, 1usize),
                    (0u32, 444usize, 12usize),
                    (0u32, 456usize, 1usize),
                    (1073741816u32, 457usize, 0usize),
                    (0u32, 457usize, 1usize),
                    (0u32, 458usize, 1usize),
                    (0u32, 459usize, 1usize),
                    (1073741816u32, 460usize, 0usize),
                    (0u32, 460usize, 1usize),
                    (0u32, 461usize, 16usize),
                    (0u32, 477usize, 1usize),
                    (1073741816u32, 478usize, 0usize),
                    (0u32, 478usize, 2usize),
                    (0u32, 480usize, 1usize),
                    (0u32, 481usize, 1usize),
                    (1073741784u32, 482usize, 0usize),
                    (0u32, 482usize, 1usize),
                    (0u32, 483usize, 8usize),
                    (0u32, 491usize, 1usize),
                    (1342177238u32, 492usize, 0usize),
                    (0u32, 492usize, 2usize),
                    (0u32, 494usize, 1usize),
                    (0u32, 495usize, 1usize),
                    (1073741784u32, 496usize, 0usize),
                    (0u32, 496usize, 1usize),
                    (0u32, 497usize, 10usize),
                    (0u32, 507usize, 1usize),
                    (1342177238u32, 508usize, 0usize),
                    (0u32, 508usize, 1usize),
                    (0u32, 509usize, 1usize),
                    (0u32, 510usize, 1usize),
                    (1073741816u32, 511usize, 0usize),
                    (0u32, 511usize, 1usize),
                    (0u32, 512usize, 17usize),
                    (0u32, 529usize, 1usize),
                    (1073741816u32, 530usize, 0usize),
                    (0u32, 530usize, 1usize),
                    (0u32, 531usize, 1usize),
                    (0u32, 532usize, 1usize),
                    (1073741816u32, 533usize, 0usize),
                    (0u32, 533usize, 1usize),
                    (0u32, 534usize, 23usize),
                    (0u32, 557usize, 1usize),
                    (1073741816u32, 558usize, 0usize),
                    (0u32, 558usize, 1usize),
                    (0u32, 559usize, 1usize),
                    (0u32, 560usize, 1usize),
                    (536870876u32, 561usize, 0usize),
                    (0u32, 561usize, 1usize),
                    (0u32, 562usize, 1usize),
                    (0u32, 563usize, 1usize),
                    (1342177238u32, 564usize, 0usize),
                    (0u32, 564usize, 4usize),
                    (0u32, 568usize, 12usize),
                    (0u32, 580usize, 1usize),
                    (805306330u32, 581usize, 0usize),
                    (0u32, 581usize, 1usize),
                    (0u32, 582usize, 1usize),
                    (0u32, 583usize, 1usize),
                    (536870876u32, 584usize, 0usize),
                    (0u32, 584usize, 1usize),
                    (0u32, 585usize, 1usize),
                    (0u32, 586usize, 1usize),
                    (1342177238u32, 587usize, 0usize),
                    (0u32, 587usize, 4usize),
                    (0u32, 591usize, 15usize),
                    (0u32, 606usize, 1usize),
                    (805306330u32, 607usize, 0usize),
                    (0u32, 607usize, 1usize),
                    (0u32, 608usize, 1usize),
                    (0u32, 609usize, 1usize),
                    (1073741816u32, 610usize, 0usize),
                    (0u32, 610usize, 1usize),
                    (0u32, 611usize, 23usize),
                    (0u32, 634usize, 1usize),
                    (1073741816u32, 635usize, 0usize),
                    (0u32, 635usize, 1usize),
                    (0u32, 636usize, 1usize),
                    (0u32, 637usize, 1usize),
                    (1073741816u32, 638usize, 0usize),
                    (0u32, 638usize, 1usize),
                    (0u32, 639usize, 31usize),
                    (0u32, 670usize, 1usize),
                    (1073741816u32, 671usize, 0usize),
                    (0u32, 671usize, 2usize),
                    (0u32, 673usize, 1usize),
                    (0u32, 674usize, 1usize),
                    (1073741784u32, 675usize, 0usize),
                    (0u32, 675usize, 1usize),
                    (0u32, 676usize, 14usize),
                    (0u32, 690usize, 1usize),
                    (1342177238u32, 691usize, 0usize),
                    (0u32, 691usize, 2usize),
                    (0u32, 693usize, 1usize),
                    (0u32, 694usize, 1usize),
                    (1073741784u32, 695usize, 0usize),
                    (0u32, 695usize, 1usize),
                    (0u32, 696usize, 18usize),
                    (0u32, 714usize, 1usize),
                    (1342177238u32, 715usize, 0usize),
                    (0u32, 715usize, 1usize),
                    (0u32, 716usize, 1usize),
                    (0u32, 717usize, 1usize),
                    (1073741816u32, 718usize, 0usize),
                    (0u32, 718usize, 1usize),
                    (0u32, 719usize, 17usize),
                    (0u32, 736usize, 1usize),
                    (1073741816u32, 737usize, 0usize),
                    (0u32, 737usize, 1usize),
                    (0u32, 738usize, 1usize),
                    (0u32, 739usize, 1usize),
                    (1073741816u32, 740usize, 0usize),
                    (0u32, 740usize, 1usize),
                    (0u32, 741usize, 23usize),
                    (0u32, 764usize, 1usize),
                    (1073741816u32, 765usize, 0usize),
                    (0u32, 765usize, 1usize),
                    (0u32, 766usize, 1usize),
                    (0u32, 767usize, 1usize),
                    (536870876u32, 768usize, 0usize),
                    (0u32, 768usize, 1usize),
                    (0u32, 769usize, 1usize),
                    (0u32, 770usize, 1usize),
                    (1342177238u32, 771usize, 0usize),
                    (0u32, 771usize, 4usize),
                    (0u32, 775usize, 12usize),
                    (0u32, 787usize, 1usize),
                    (805306330u32, 788usize, 0usize),
                    (0u32, 788usize, 1usize),
                    (0u32, 789usize, 1usize),
                    (0u32, 790usize, 1usize),
                    (536870876u32, 791usize, 0usize),
                    (0u32, 791usize, 1usize),
                    (0u32, 792usize, 1usize),
                    (0u32, 793usize, 1usize),
                    (1342177238u32, 794usize, 0usize),
                    (0u32, 794usize, 4usize),
                    (0u32, 798usize, 15usize),
                    (0u32, 813usize, 1usize),
                    (805306330u32, 814usize, 0usize),
                    (0u32, 814usize, 1usize),
                    (0u32, 815usize, 1usize),
                    (0u32, 816usize, 1usize),
                    (1073741816u32, 817usize, 0usize),
                    (0u32, 817usize, 1usize),
                    (0u32, 818usize, 23usize),
                    (0u32, 841usize, 1usize),
                    (1073741816u32, 842usize, 0usize),
                    (0u32, 842usize, 1usize),
                    (0u32, 843usize, 1usize),
                    (0u32, 844usize, 1usize),
                    (1073741816u32, 845usize, 0usize),
                    (0u32, 845usize, 1usize),
                    (0u32, 846usize, 31usize),
                    (0u32, 877usize, 1usize),
                    (1073741816u32, 878usize, 0usize),
                    (0u32, 878usize, 2usize),
                    (0u32, 880usize, 1usize),
                    (0u32, 881usize, 1usize),
                    (1073741784u32, 882usize, 0usize),
                    (0u32, 882usize, 1usize),
                    (0u32, 883usize, 14usize),
                    (0u32, 897usize, 1usize),
                    (1342177238u32, 898usize, 0usize),
                    (0u32, 898usize, 2usize),
                    (0u32, 900usize, 1usize),
                    (0u32, 901usize, 1usize),
                    (1073741784u32, 902usize, 0usize),
                    (0u32, 902usize, 1usize),
                    (0u32, 903usize, 18usize),
                    (0u32, 921usize, 1usize),
                    (1342177238u32, 922usize, 0usize),
                    (0u32, 922usize, 1usize),
                    (0u32, 923usize, 1usize),
                    (0u32, 924usize, 1usize),
                    (1073741816u32, 925usize, 0usize),
                    (0u32, 925usize, 1usize),
                    (0u32, 926usize, 17usize),
                    (0u32, 943usize, 1usize),
                    (1073741816u32, 944usize, 0usize),
                    (0u32, 944usize, 1usize),
                    (0u32, 945usize, 1usize),
                    (0u32, 946usize, 1usize),
                    (1073741816u32, 947usize, 0usize),
                    (0u32, 947usize, 1usize),
                    (0u32, 948usize, 23usize),
                    (0u32, 971usize, 1usize),
                    (1073741816u32, 972usize, 0usize),
                    (0u32, 972usize, 1usize),
                    (0u32, 973usize, 1usize),
                    (0u32, 974usize, 1usize),
                    (536870876u32, 975usize, 0usize),
                    (0u32, 975usize, 1usize),
                    (0u32, 976usize, 1usize),
                    (0u32, 977usize, 1usize),
                    (1342177238u32, 978usize, 0usize),
                    (0u32, 978usize, 4usize),
                    (0u32, 982usize, 12usize),
                    (0u32, 994usize, 1usize),
                    (805306330u32, 995usize, 0usize),
                    (0u32, 995usize, 1usize),
                    (0u32, 996usize, 1usize),
                    (0u32, 997usize, 1usize),
                    (536870876u32, 998usize, 0usize),
                    (0u32, 998usize, 1usize),
                    (0u32, 999usize, 1usize),
                    (0u32, 1000usize, 1usize),
                    (1342177238u32, 1001usize, 0usize),
                    (0u32, 1001usize, 4usize),
                    (0u32, 1005usize, 15usize),
                    (0u32, 1020usize, 1usize),
                    (805306330u32, 1021usize, 0usize),
                    (0u32, 1021usize, 1usize),
                    (0u32, 1022usize, 1usize),
                    (0u32, 1023usize, 1usize),
                    (1073741816u32, 1024usize, 0usize),
                    (0u32, 1024usize, 1usize),
                    (0u32, 1025usize, 23usize),
                    (0u32, 1048usize, 1usize),
                    (1073741816u32, 1049usize, 0usize),
                    (0u32, 1049usize, 1usize),
                    (0u32, 1050usize, 1usize),
                    (0u32, 1051usize, 1usize),
                    (1073741816u32, 1052usize, 0usize),
                    (0u32, 1052usize, 1usize),
                    (0u32, 1053usize, 31usize),
                    (0u32, 1084usize, 1usize),
                    (1073741816u32, 1085usize, 0usize),
                    (0u32, 1085usize, 2usize),
                    (0u32, 1087usize, 1usize),
                    (0u32, 1088usize, 1usize),
                    (1073741784u32, 1089usize, 0usize),
                    (0u32, 1089usize, 1usize),
                    (0u32, 1090usize, 14usize),
                    (0u32, 1104usize, 1usize),
                    (1342177238u32, 1105usize, 0usize),
                    (0u32, 1105usize, 2usize),
                    (0u32, 1107usize, 1usize),
                    (0u32, 1108usize, 1usize),
                    (1073741784u32, 1109usize, 0usize),
                    (0u32, 1109usize, 1usize),
                    (0u32, 1110usize, 18usize),
                    (0u32, 1128usize, 1usize),
                    (1342177238u32, 1129usize, 0usize),
                    (0u32, 1129usize, 1usize),
                    (0u32, 1130usize, 1usize),
                    (0u32, 1131usize, 1usize),
                    (1073741816u32, 1132usize, 0usize),
                    (0u32, 1132usize, 1usize),
                    (0u32, 1133usize, 17usize),
                    (0u32, 1150usize, 1usize),
                    (1073741816u32, 1151usize, 0usize),
                    (0u32, 1151usize, 1usize),
                    (0u32, 1152usize, 1usize),
                    (0u32, 1153usize, 1usize),
                    (1073741816u32, 1154usize, 0usize),
                    (0u32, 1154usize, 1usize),
                    (0u32, 1155usize, 23usize),
                    (0u32, 1178usize, 1usize),
                    (1073741816u32, 1179usize, 0usize),
                    (0u32, 1179usize, 1usize),
                    (0u32, 1180usize, 1usize),
                    (0u32, 1181usize, 1usize),
                    (536870876u32, 1182usize, 0usize),
                    (0u32, 1182usize, 1usize),
                    (0u32, 1183usize, 1usize),
                    (0u32, 1184usize, 1usize),
                    (1342177238u32, 1185usize, 0usize),
                    (0u32, 1185usize, 4usize),
                    (0u32, 1189usize, 12usize),
                    (0u32, 1201usize, 1usize),
                    (805306330u32, 1202usize, 0usize),
                    (0u32, 1202usize, 1usize),
                    (0u32, 1203usize, 1usize),
                    (0u32, 1204usize, 1usize),
                    (536870876u32, 1205usize, 0usize),
                    (0u32, 1205usize, 1usize),
                    (0u32, 1206usize, 1usize),
                    (0u32, 1207usize, 1usize),
                    (1342177238u32, 1208usize, 0usize),
                    (0u32, 1208usize, 4usize),
                    (0u32, 1212usize, 15usize),
                    (0u32, 1227usize, 1usize),
                    (805306330u32, 1228usize, 0usize),
                    (0u32, 1228usize, 1usize),
                    (0u32, 1229usize, 1usize),
                    (0u32, 1230usize, 1usize),
                    (1073741816u32, 1231usize, 0usize),
                    (0u32, 1231usize, 1usize),
                    (0u32, 1232usize, 23usize),
                    (0u32, 1255usize, 1usize),
                    (1073741816u32, 1256usize, 0usize),
                    (0u32, 1256usize, 1usize),
                    (0u32, 1257usize, 1usize),
                    (0u32, 1258usize, 1usize),
                    (1073741816u32, 1259usize, 0usize),
                    (0u32, 1259usize, 1usize),
                    (0u32, 1260usize, 31usize),
                    (0u32, 1291usize, 1usize),
                    (1073741816u32, 1292usize, 0usize),
                    (0u32, 1292usize, 2usize),
                    (0u32, 1294usize, 1usize),
                    (0u32, 1295usize, 1usize),
                    (1073741784u32, 1296usize, 0usize),
                    (0u32, 1296usize, 1usize),
                    (0u32, 1297usize, 14usize),
                    (0u32, 1311usize, 1usize),
                    (1342177238u32, 1312usize, 0usize),
                    (0u32, 1312usize, 2usize),
                    (0u32, 1314usize, 1usize),
                    (0u32, 1315usize, 1usize),
                    (1073741784u32, 1316usize, 0usize),
                    (0u32, 1316usize, 1usize),
                    (0u32, 1317usize, 18usize),
                    (0u32, 1335usize, 1usize),
                    (1342177238u32, 1336usize, 0usize),
                    (0u32, 1336usize, 1usize),
                    (0u32, 1337usize, 1usize),
                    (0u32, 1338usize, 1usize),
                    (1073741784u32, 1339usize, 0usize),
                    (0u32, 1339usize, 2usize),
                    (0u32, 1341usize, 14usize),
                    (0u32, 1355usize, 1usize),
                    (1342177238u32, 1356usize, 0usize),
                    (0u32, 1356usize, 1usize),
                    (0u32, 1357usize, 1usize),
                    (0u32, 1358usize, 1usize),
                    (1073741784u32, 1359usize, 0usize),
                    (0u32, 1359usize, 1usize),
                    (0u32, 1360usize, 24usize),
                    (0u32, 1384usize, 1usize),
                    (1342177238u32, 1385usize, 0usize),
                    (0u32, 1385usize, 1usize),
                    (0u32, 1386usize, 1usize),
                    (0u32, 1387usize, 1usize),
                    (1073741784u32, 1388usize, 0usize),
                    (0u32, 1388usize, 2usize),
                    (0u32, 1390usize, 18usize),
                    (0u32, 1408usize, 1usize),
                    (1342177238u32, 1409usize, 0usize),
                    (0u32, 1409usize, 1usize),
                    (0u32, 1410usize, 1usize),
                    (0u32, 1411usize, 1usize),
                    (1073741784u32, 1412usize, 0usize),
                    (0u32, 1412usize, 1usize),
                    (0u32, 1413usize, 32usize),
                    (0u32, 1445usize, 1usize),
                    (1342177238u32, 1446usize, 0usize),
                    (0u32, 1446usize, 1usize),
                    (0u32, 1447usize, 1usize),
                    (0u32, 1448usize, 1usize),
                    (1073741784u32, 1449usize, 0usize),
                    (0u32, 1449usize, 2usize),
                    (0u32, 1451usize, 14usize),
                    (0u32, 1465usize, 1usize),
                    (1342177238u32, 1466usize, 0usize),
                    (0u32, 1466usize, 1usize),
                    (0u32, 1467usize, 1usize),
                    (0u32, 1468usize, 1usize),
                    (1073741784u32, 1469usize, 0usize),
                    (0u32, 1469usize, 1usize),
                    (0u32, 1470usize, 24usize),
                    (0u32, 1494usize, 1usize),
                    (1342177238u32, 1495usize, 0usize),
                    (0u32, 1495usize, 1usize),
                    (0u32, 1496usize, 1usize),
                    (0u32, 1497usize, 1usize),
                    (1073741784u32, 1498usize, 0usize),
                    (0u32, 1498usize, 2usize),
                    (0u32, 1500usize, 18usize),
                    (0u32, 1518usize, 1usize),
                    (1342177238u32, 1519usize, 0usize),
                    (0u32, 1519usize, 1usize),
                    (0u32, 1520usize, 1usize),
                    (0u32, 1521usize, 1usize),
                    (1073741784u32, 1522usize, 0usize),
                    (0u32, 1522usize, 1usize),
                    (0u32, 1523usize, 32usize),
                    (0u32, 1555usize, 1usize),
                    (1342177238u32, 1556usize, 0usize),
                    (0u32, 1556usize, 1usize),
                    (0u32, 1557usize, 1usize),
                    (0u32, 1558usize, 1usize),
                    (1073741784u32, 1559usize, 0usize),
                    (0u32, 1559usize, 2usize),
                    (0u32, 1561usize, 14usize),
                    (0u32, 1575usize, 1usize),
                    (1342177238u32, 1576usize, 0usize),
                    (0u32, 1576usize, 1usize),
                    (0u32, 1577usize, 1usize),
                    (0u32, 1578usize, 1usize),
                    (1073741784u32, 1579usize, 0usize),
                    (0u32, 1579usize, 1usize),
                    (0u32, 1580usize, 24usize),
                    (0u32, 1604usize, 1usize),
                    (1342177238u32, 1605usize, 0usize),
                    (0u32, 1605usize, 1usize),
                    (0u32, 1606usize, 1usize),
                    (0u32, 1607usize, 1usize),
                    (1073741784u32, 1608usize, 0usize),
                    (0u32, 1608usize, 2usize),
                    (0u32, 1610usize, 18usize),
                    (0u32, 1628usize, 1usize),
                    (1342177238u32, 1629usize, 0usize),
                    (0u32, 1629usize, 1usize),
                    (0u32, 1630usize, 1usize),
                    (0u32, 1631usize, 1usize),
                    (1073741784u32, 1632usize, 0usize),
                    (0u32, 1632usize, 1usize),
                    (0u32, 1633usize, 32usize),
                    (0u32, 1665usize, 1usize),
                    (1342177238u32, 1666usize, 0usize),
                    (0u32, 1666usize, 1usize),
                    (0u32, 1667usize, 1usize),
                    (0u32, 1668usize, 1usize),
                    (1073741784u32, 1669usize, 0usize),
                    (0u32, 1669usize, 2usize),
                    (0u32, 1671usize, 14usize),
                    (0u32, 1685usize, 1usize),
                    (1342177238u32, 1686usize, 0usize),
                    (0u32, 1686usize, 1usize),
                    (0u32, 1687usize, 1usize),
                    (0u32, 1688usize, 1usize),
                    (1073741784u32, 1689usize, 0usize),
                    (0u32, 1689usize, 1usize),
                    (0u32, 1690usize, 24usize),
                    (0u32, 1714usize, 1usize),
                    (1342177238u32, 1715usize, 0usize),
                    (0u32, 1715usize, 1usize),
                    (0u32, 1716usize, 1usize),
                    (0u32, 1717usize, 1usize),
                    (1073741784u32, 1718usize, 0usize),
                    (0u32, 1718usize, 2usize),
                    (0u32, 1720usize, 18usize),
                    (0u32, 1738usize, 1usize),
                    (1342177238u32, 1739usize, 0usize),
                    (0u32, 1739usize, 1usize),
                    (0u32, 1740usize, 1usize),
                    (0u32, 1741usize, 1usize),
                    (1073741784u32, 1742usize, 0usize),
                    (0u32, 1742usize, 1usize),
                    (0u32, 1743usize, 32usize),
                    (0u32, 1775usize, 1usize),
                    (1342177238u32, 1776usize, 0usize),
                    (0u32, 1776usize, 1usize),
                    (0u32, 1777usize, 1usize),
                    (0u32, 1778usize, 1usize),
                    (1342177238u32, 1779usize, 0usize),
                    (0u32, 1779usize, 1usize),
                    (0u32, 1780usize, 2usize),
                    (0u32, 1782usize, 1usize),
                    (1073741784u32, 1783usize, 0usize),
                    (0u32, 1783usize, 1usize),
                    (0u32, 1784usize, 1usize),
                    (0u32, 1785usize, 1usize),
                    (1073741816u32, 1786usize, 0usize),
                    (0u32, 1786usize, 1usize),
                    (0u32, 1787usize, 2usize),
                    (0u32, 1789usize, 1usize),
                    (1073741816u32, 1790usize, 0usize),
                    (0u32, 1790usize, 1usize),
                    (0u32, 1791usize, 1usize),
                    (0u32, 1792usize, 1usize),
                    (1342177238u32, 1793usize, 0usize),
                    (0u32, 1793usize, 1usize),
                    (0u32, 1794usize, 2usize),
                    (0u32, 1796usize, 1usize),
                    (1073741784u32, 1797usize, 0usize),
                    (0u32, 1797usize, 1usize),
                    (0u32, 1798usize, 1usize),
                    (0u32, 1799usize, 1usize),
                    (1073741816u32, 1800usize, 0usize),
                    (0u32, 1800usize, 1usize),
                    (0u32, 1801usize, 2usize),
                    (0u32, 1803usize, 1usize),
                    (1073741816u32, 1804usize, 0usize),
                    (0u32, 1804usize, 1usize),
                    (0u32, 1805usize, 1usize),
                    (0u32, 1806usize, 1usize),
                    (1342177238u32, 1807usize, 0usize),
                    (0u32, 1807usize, 1usize),
                    (0u32, 1808usize, 2usize),
                    (0u32, 1810usize, 1usize),
                    (1073741784u32, 1811usize, 0usize),
                    (0u32, 1811usize, 1usize),
                    (0u32, 1812usize, 1usize),
                    (0u32, 1813usize, 1usize),
                    (1073741816u32, 1814usize, 0usize),
                    (0u32, 1814usize, 1usize),
                    (0u32, 1815usize, 2usize),
                    (0u32, 1817usize, 1usize),
                    (1073741816u32, 1818usize, 0usize),
                    (0u32, 1818usize, 1usize),
                    (0u32, 1819usize, 1usize),
                    (0u32, 1820usize, 1usize),
                    (1342177238u32, 1821usize, 0usize),
                    (0u32, 1821usize, 1usize),
                    (0u32, 1822usize, 2usize),
                    (0u32, 1824usize, 1usize),
                    (1073741784u32, 1825usize, 0usize),
                    (0u32, 1825usize, 1usize),
                    (0u32, 1826usize, 1usize),
                    (0u32, 1827usize, 1usize),
                    (1073741816u32, 1828usize, 0usize),
                    (0u32, 1828usize, 1usize),
                    (0u32, 1829usize, 2usize),
                    (0u32, 1831usize, 1usize),
                    (1073741816u32, 1832usize, 0usize),
                    (0u32, 1832usize, 1usize),
                    (0u32, 1833usize, 1usize),
                    (0u32, 1834usize, 1usize),
                    (1342177238u32, 1835usize, 0usize),
                    (0u32, 1835usize, 1usize),
                    (0u32, 1836usize, 2usize),
                    (0u32, 1838usize, 1usize),
                    (1073741784u32, 1839usize, 0usize),
                    (0u32, 1839usize, 1usize),
                    (0u32, 1840usize, 1usize),
                    (0u32, 1841usize, 1usize),
                    (1073741816u32, 1842usize, 0usize),
                    (0u32, 1842usize, 1usize),
                    (0u32, 1843usize, 2usize),
                    (0u32, 1845usize, 1usize),
                    (1073741816u32, 1846usize, 0usize),
                    (0u32, 1846usize, 1usize),
                    (0u32, 1847usize, 1usize),
                    (0u32, 1848usize, 1usize),
                    (1342177238u32, 1849usize, 0usize),
                    (0u32, 1849usize, 1usize),
                    (0u32, 1850usize, 2usize),
                    (0u32, 1852usize, 1usize),
                    (1073741784u32, 1853usize, 0usize),
                    (0u32, 1853usize, 1usize),
                    (0u32, 1854usize, 1usize),
                    (0u32, 1855usize, 1usize),
                    (1073741816u32, 1856usize, 0usize),
                    (0u32, 1856usize, 1usize),
                    (0u32, 1857usize, 2usize),
                    (0u32, 1859usize, 1usize),
                    (1073741816u32, 1860usize, 0usize),
                    (0u32, 1860usize, 1usize),
                    (0u32, 1861usize, 1usize),
                    (0u32, 1862usize, 1usize),
                    (1342177238u32, 1863usize, 0usize),
                    (0u32, 1863usize, 1usize),
                    (0u32, 1864usize, 2usize),
                    (0u32, 1866usize, 1usize),
                    (1073741784u32, 1867usize, 0usize),
                    (0u32, 1867usize, 1usize),
                    (0u32, 1868usize, 1usize),
                    (0u32, 1869usize, 1usize),
                    (1073741816u32, 1870usize, 0usize),
                    (0u32, 1870usize, 1usize),
                    (0u32, 1871usize, 2usize),
                    (0u32, 1873usize, 1usize),
                    (1073741816u32, 1874usize, 0usize),
                    (0u32, 1874usize, 1usize),
                    (0u32, 1875usize, 1usize),
                    (0u32, 1876usize, 1usize),
                    (1342177238u32, 1877usize, 0usize),
                    (0u32, 1877usize, 1usize),
                    (0u32, 1878usize, 2usize),
                    (0u32, 1880usize, 1usize),
                    (1073741784u32, 1881usize, 0usize),
                    (0u32, 1881usize, 1usize),
                    (0u32, 1882usize, 1usize),
                    (0u32, 1883usize, 1usize),
                    (1073741816u32, 1884usize, 0usize),
                ];
                const VL_TERMS: [(u32, usize); 1884usize] = [
                    (268435454u32, 360usize),
                    (268435454u32, 358usize),
                    (268435454u32, 361usize),
                    (16777216u32, 284usize),
                    (1996488705u32, 360usize),
                    (16777216u32, 241usize),
                    (16777216u32, 257usize),
                    (16777216u32, 322usize),
                    (1744831011u32, 354usize),
                    (1476396101u32, 355usize),
                    (1996488705u32, 358usize),
                    (268435454u32, 362usize),
                    (268435454u32, 363usize),
                    (268435454u32, 359usize),
                    (268435454u32, 364usize),
                    (16777216u32, 285usize),
                    (1996488705u32, 363usize),
                    (16777216u32, 243usize),
                    (16777216u32, 259usize),
                    (16777216u32, 323usize),
                    (16777216u32, 354usize),
                    (33554432u32, 355usize),
                    (1744831011u32, 356usize),
                    (1476396101u32, 357usize),
                    (1996488705u32, 359usize),
                    (268435454u32, 365usize),
                    (268435454u32, 372usize),
                    (268435454u32, 368usize),
                    (268435454u32, 374usize),
                    (268435454u32, 373usize),
                    (268435454u32, 369usize),
                    (268435454u32, 375usize),
                    (1048576u32, 257usize),
                    (2012217345u32, 372usize),
                    (2004877313u32, 373usize),
                    (1048576u32, 272usize),
                    (1048576u32, 364usize),
                    (268435456u32, 365usize),
                    (1744830499u32, 366usize),
                    (2012217345u32, 368usize),
                    (2004877313u32, 369usize),
                    (268435454u32, 376usize),
                    (268435454u32, 377usize),
                    (268435454u32, 370usize),
                    (268435454u32, 379usize),
                    (268435454u32, 378usize),
                    (268435454u32, 371usize),
                    (268435454u32, 380usize),
                    (1048576u32, 259usize),
                    (2012217345u32, 377usize),
                    (2004877313u32, 378usize),
                    (1048576u32, 273usize),
                    (1048576u32, 361usize),
                    (268435456u32, 362usize),
                    (1048576u32, 366usize),
                    (1744830499u32, 367usize),
                    (2012217345u32, 370usize),
                    (2004877313u32, 371usize),
                    (268435454u32, 381usize),
                    (268435454u32, 364usize),
                    (268435454u32, 386usize),
                    (268435454u32, 388usize),
                    (268435454u32, 365usize),
                    (16777216u32, 241usize),
                    (16777216u32, 257usize),
                    (16777216u32, 322usize),
                    (16777216u32, 324usize),
                    (1744831011u32, 354usize),
                    (1476396101u32, 355usize),
                    (16777216u32, 376usize),
                    (268435456u32, 379usize),
                    (134217727u32, 380usize),
                    (1744831011u32, 382usize),
                    (1476396101u32, 383usize),
                    (1996488705u32, 386usize),
                    (268435454u32, 389usize),
                    (268435454u32, 361usize),
                    (268435454u32, 387usize),
                    (268435454u32, 390usize),
                    (268435454u32, 362usize),
                    (16777216u32, 243usize),
                    (16777216u32, 259usize),
                    (16777216u32, 323usize),
                    (16777216u32, 325usize),
                    (16777216u32, 354usize),
                    (33554432u32, 355usize),
                    (1744831011u32, 356usize),
                    (1476396101u32, 357usize),
                    (268435456u32, 374usize),
                    (134217727u32, 375usize),
                    (16777216u32, 381usize),
                    (16777216u32, 382usize),
                    (33554432u32, 383usize),
                    (1744831011u32, 384usize),
                    (1476396101u32, 385usize),
                    (1996488705u32, 387usize),
                    (268435454u32, 391usize),
                    (268435454u32, 376usize),
                    (268435422u32, 379usize),
                    (268435454u32, 394usize),
                    (268435454u32, 396usize),
                    (268435454u32, 380usize),
                    (33554432u32, 272usize),
                    (33554432u32, 364usize),
                    (536870908u32, 365usize),
                    (1476396101u32, 366usize),
                    (33554432u32, 389usize),
                    (536870908u32, 390usize),
                    (1476396101u32, 392usize),
                    (1979711489u32, 394usize),
                    (268435454u32, 397usize),
                    (268435422u32, 374usize),
                    (268435454u32, 381usize),
                    (268435454u32, 395usize),
                    (268435454u32, 398usize),
                    (268435454u32, 375usize),
                    (33554432u32, 273usize),
                    (33554432u32, 361usize),
                    (536870908u32, 362usize),
                    (33554432u32, 366usize),
                    (1476396101u32, 367usize),
                    (536870908u32, 388usize),
                    (33554432u32, 391usize),
                    (33554432u32, 392usize),
                    (1476396101u32, 393usize),
                    (1979711489u32, 395usize),
                    (268435454u32, 399usize),
                    (268435454u32, 406usize),
                    (268435454u32, 404usize),
                    (268435454u32, 407usize),
                    (16777216u32, 280usize),
                    (1996488705u32, 406usize),
                    (16777216u32, 245usize),
                    (16777216u32, 261usize),
                    (16777216u32, 326usize),
                    (1744831011u32, 400usize),
                    (1476396101u32, 401usize),
                    (1996488705u32, 404usize),
                    (268435454u32, 408usize),
                    (268435454u32, 409usize),
                    (268435454u32, 405usize),
                    (268435454u32, 410usize),
                    (16777216u32, 281usize),
                    (1996488705u32, 409usize),
                    (16777216u32, 247usize),
                    (16777216u32, 263usize),
                    (16777216u32, 327usize),
                    (16777216u32, 400usize),
                    (33554432u32, 401usize),
                    (1744831011u32, 402usize),
                    (1476396101u32, 403usize),
                    (1996488705u32, 405usize),
                    (268435454u32, 411usize),
                    (268435454u32, 418usize),
                    (268435454u32, 414usize),
                    (268435454u32, 420usize),
                    (268435454u32, 419usize),
                    (268435454u32, 415usize),
                    (268435454u32, 421usize),
                    (1048576u32, 261usize),
                    (2012217345u32, 418usize),
                    (2004877313u32, 419usize),
                    (1048576u32, 274usize),
                    (1048576u32, 410usize),
                    (268435456u32, 411usize),
                    (1744830499u32, 412usize),
                    (2012217345u32, 414usize),
                    (2004877313u32, 415usize),
                    (268435454u32, 422usize),
                    (268435454u32, 423usize),
                    (268435454u32, 416usize),
                    (268435454u32, 425usize),
                    (268435454u32, 424usize),
                    (268435454u32, 417usize),
                    (268435454u32, 426usize),
                    (1048576u32, 263usize),
                    (2012217345u32, 423usize),
                    (2004877313u32, 424usize),
                    (1048576u32, 275usize),
                    (1048576u32, 407usize),
                    (268435456u32, 408usize),
                    (1048576u32, 412usize),
                    (1744830499u32, 413usize),
                    (2012217345u32, 416usize),
                    (2004877313u32, 417usize),
                    (268435454u32, 427usize),
                    (268435454u32, 410usize),
                    (268435454u32, 432usize),
                    (268435454u32, 434usize),
                    (268435454u32, 411usize),
                    (16777216u32, 245usize),
                    (16777216u32, 261usize),
                    (16777216u32, 326usize),
                    (16777216u32, 328usize),
                    (1744831011u32, 400usize),
                    (1476396101u32, 401usize),
                    (16777216u32, 422usize),
                    (268435456u32, 425usize),
                    (134217727u32, 426usize),
                    (1744831011u32, 428usize),
                    (1476396101u32, 429usize),
                    (1996488705u32, 432usize),
                    (268435454u32, 435usize),
                    (268435454u32, 407usize),
                    (268435454u32, 433usize),
                    (268435454u32, 436usize),
                    (268435454u32, 408usize),
                    (16777216u32, 247usize),
                    (16777216u32, 263usize),
                    (16777216u32, 327usize),
                    (16777216u32, 329usize),
                    (16777216u32, 400usize),
                    (33554432u32, 401usize),
                    (1744831011u32, 402usize),
                    (1476396101u32, 403usize),
                    (268435456u32, 420usize),
                    (134217727u32, 421usize),
                    (16777216u32, 427usize),
                    (16777216u32, 428usize),
                    (33554432u32, 429usize),
                    (1744831011u32, 430usize),
                    (1476396101u32, 431usize),
                    (1996488705u32, 433usize),
                    (268435454u32, 437usize),
                    (268435454u32, 422usize),
                    (268435422u32, 425usize),
                    (268435454u32, 440usize),
                    (268435454u32, 442usize),
                    (268435454u32, 426usize),
                    (33554432u32, 274usize),
                    (33554432u32, 410usize),
                    (536870908u32, 411usize),
                    (1476396101u32, 412usize),
                    (33554432u32, 435usize),
                    (536870908u32, 436usize),
                    (1476396101u32, 438usize),
                    (1979711489u32, 440usize),
                    (268435454u32, 443usize),
                    (268435422u32, 420usize),
                    (268435454u32, 427usize),
                    (268435454u32, 441usize),
                    (268435454u32, 444usize),
                    (268435454u32, 421usize),
                    (33554432u32, 275usize),
                    (33554432u32, 407usize),
                    (536870908u32, 408usize),
                    (33554432u32, 412usize),
                    (1476396101u32, 413usize),
                    (536870908u32, 434usize),
                    (33554432u32, 437usize),
                    (33554432u32, 438usize),
                    (1476396101u32, 439usize),
                    (1979711489u32, 441usize),
                    (268435454u32, 445usize),
                    (268435454u32, 452usize),
                    (268435454u32, 450usize),
                    (268435454u32, 453usize),
                    (16777216u32, 286usize),
                    (1996488705u32, 452usize),
                    (16777216u32, 249usize),
                    (16777216u32, 265usize),
                    (16777216u32, 330usize),
                    (1744831011u32, 446usize),
                    (1476396101u32, 447usize),
                    (1996488705u32, 450usize),
                    (268435454u32, 454usize),
                    (268435454u32, 455usize),
                    (268435454u32, 451usize),
                    (268435454u32, 456usize),
                    (16777216u32, 287usize),
                    (1996488705u32, 455usize),
                    (16777216u32, 251usize),
                    (16777216u32, 267usize),
                    (16777216u32, 331usize),
                    (16777216u32, 446usize),
                    (33554432u32, 447usize),
                    (1744831011u32, 448usize),
                    (1476396101u32, 449usize),
                    (1996488705u32, 451usize),
                    (268435454u32, 457usize),
                    (268435454u32, 464usize),
                    (268435454u32, 460usize),
                    (268435454u32, 466usize),
                    (268435454u32, 465usize),
                    (268435454u32, 461usize),
                    (268435454u32, 467usize),
                    (1048576u32, 265usize),
                    (2012217345u32, 464usize),
                    (2004877313u32, 465usize),
                    (1048576u32, 276usize),
                    (1048576u32, 456usize),
                    (268435456u32, 457usize),
                    (1744830499u32, 458usize),
                    (2012217345u32, 460usize),
                    (2004877313u32, 461usize),
                    (268435454u32, 468usize),
                    (268435454u32, 469usize),
                    (268435454u32, 462usize),
                    (268435454u32, 471usize),
                    (268435454u32, 470usize),
                    (268435454u32, 463usize),
                    (268435454u32, 472usize),
                    (1048576u32, 267usize),
                    (2012217345u32, 469usize),
                    (2004877313u32, 470usize),
                    (1048576u32, 277usize),
                    (1048576u32, 453usize),
                    (268435456u32, 454usize),
                    (1048576u32, 458usize),
                    (1744830499u32, 459usize),
                    (2012217345u32, 462usize),
                    (2004877313u32, 463usize),
                    (268435454u32, 473usize),
                    (268435454u32, 456usize),
                    (268435454u32, 478usize),
                    (268435454u32, 480usize),
                    (268435454u32, 457usize),
                    (16777216u32, 249usize),
                    (16777216u32, 265usize),
                    (16777216u32, 330usize),
                    (16777216u32, 332usize),
                    (1744831011u32, 446usize),
                    (1476396101u32, 447usize),
                    (16777216u32, 468usize),
                    (268435456u32, 471usize),
                    (134217727u32, 472usize),
                    (1744831011u32, 474usize),
                    (1476396101u32, 475usize),
                    (1996488705u32, 478usize),
                    (268435454u32, 481usize),
                    (268435454u32, 453usize),
                    (268435454u32, 479usize),
                    (268435454u32, 482usize),
                    (268435454u32, 454usize),
                    (16777216u32, 251usize),
                    (16777216u32, 267usize),
                    (16777216u32, 331usize),
                    (16777216u32, 333usize),
                    (16777216u32, 446usize),
                    (33554432u32, 447usize),
                    (1744831011u32, 448usize),
                    (1476396101u32, 449usize),
                    (268435456u32, 466usize),
                    (134217727u32, 467usize),
                    (16777216u32, 473usize),
                    (16777216u32, 474usize),
                    (33554432u32, 475usize),
                    (1744831011u32, 476usize),
                    (1476396101u32, 477usize),
                    (1996488705u32, 479usize),
                    (268435454u32, 483usize),
                    (268435454u32, 468usize),
                    (268435422u32, 471usize),
                    (268435454u32, 486usize),
                    (268435454u32, 488usize),
                    (268435454u32, 472usize),
                    (33554432u32, 276usize),
                    (33554432u32, 456usize),
                    (536870908u32, 457usize),
                    (1476396101u32, 458usize),
                    (33554432u32, 481usize),
                    (536870908u32, 482usize),
                    (1476396101u32, 484usize),
                    (1979711489u32, 486usize),
                    (268435454u32, 489usize),
                    (268435422u32, 466usize),
                    (268435454u32, 473usize),
                    (268435454u32, 487usize),
                    (268435454u32, 490usize),
                    (268435454u32, 467usize),
                    (33554432u32, 277usize),
                    (33554432u32, 453usize),
                    (536870908u32, 454usize),
                    (33554432u32, 458usize),
                    (1476396101u32, 459usize),
                    (536870908u32, 480usize),
                    (33554432u32, 483usize),
                    (33554432u32, 484usize),
                    (1476396101u32, 485usize),
                    (1979711489u32, 487usize),
                    (268435454u32, 491usize),
                    (268435454u32, 498usize),
                    (268435454u32, 496usize),
                    (268435454u32, 499usize),
                    (16777216u32, 282usize),
                    (1996488705u32, 498usize),
                    (16777216u32, 253usize),
                    (16777216u32, 269usize),
                    (16777216u32, 334usize),
                    (1744831011u32, 492usize),
                    (1476396101u32, 493usize),
                    (1996488705u32, 496usize),
                    (268435454u32, 500usize),
                    (268435454u32, 501usize),
                    (268435454u32, 497usize),
                    (268435454u32, 502usize),
                    (16777216u32, 283usize),
                    (1996488705u32, 501usize),
                    (16777216u32, 255usize),
                    (16777216u32, 271usize),
                    (16777216u32, 335usize),
                    (16777216u32, 492usize),
                    (33554432u32, 493usize),
                    (1744831011u32, 494usize),
                    (1476396101u32, 495usize),
                    (1996488705u32, 497usize),
                    (268435454u32, 503usize),
                    (268435454u32, 510usize),
                    (268435454u32, 506usize),
                    (268435454u32, 512usize),
                    (268435454u32, 511usize),
                    (268435454u32, 507usize),
                    (268435454u32, 513usize),
                    (1048576u32, 269usize),
                    (2012217345u32, 510usize),
                    (2004877313u32, 511usize),
                    (1048576u32, 278usize),
                    (1048576u32, 502usize),
                    (268435456u32, 503usize),
                    (1744830499u32, 504usize),
                    (2012217345u32, 506usize),
                    (2004877313u32, 507usize),
                    (268435454u32, 514usize),
                    (268435454u32, 515usize),
                    (268435454u32, 508usize),
                    (268435454u32, 517usize),
                    (268435454u32, 516usize),
                    (268435454u32, 509usize),
                    (268435454u32, 518usize),
                    (1048576u32, 271usize),
                    (2012217345u32, 515usize),
                    (2004877313u32, 516usize),
                    (1048576u32, 279usize),
                    (1048576u32, 499usize),
                    (268435456u32, 500usize),
                    (1048576u32, 504usize),
                    (1744830499u32, 505usize),
                    (2012217345u32, 508usize),
                    (2004877313u32, 509usize),
                    (268435454u32, 519usize),
                    (268435454u32, 502usize),
                    (268435454u32, 524usize),
                    (268435454u32, 526usize),
                    (268435454u32, 503usize),
                    (16777216u32, 253usize),
                    (16777216u32, 269usize),
                    (16777216u32, 334usize),
                    (16777216u32, 336usize),
                    (1744831011u32, 492usize),
                    (1476396101u32, 493usize),
                    (16777216u32, 514usize),
                    (268435456u32, 517usize),
                    (134217727u32, 518usize),
                    (1744831011u32, 520usize),
                    (1476396101u32, 521usize),
                    (1996488705u32, 524usize),
                    (268435454u32, 527usize),
                    (268435454u32, 499usize),
                    (268435454u32, 525usize),
                    (268435454u32, 528usize),
                    (268435454u32, 500usize),
                    (16777216u32, 255usize),
                    (16777216u32, 271usize),
                    (16777216u32, 335usize),
                    (16777216u32, 337usize),
                    (16777216u32, 492usize),
                    (33554432u32, 493usize),
                    (1744831011u32, 494usize),
                    (1476396101u32, 495usize),
                    (268435456u32, 512usize),
                    (134217727u32, 513usize),
                    (16777216u32, 519usize),
                    (16777216u32, 520usize),
                    (33554432u32, 521usize),
                    (1744831011u32, 522usize),
                    (1476396101u32, 523usize),
                    (1996488705u32, 525usize),
                    (268435454u32, 529usize),
                    (268435454u32, 514usize),
                    (268435422u32, 517usize),
                    (268435454u32, 532usize),
                    (268435454u32, 534usize),
                    (268435454u32, 518usize),
                    (33554432u32, 278usize),
                    (33554432u32, 502usize),
                    (536870908u32, 503usize),
                    (1476396101u32, 504usize),
                    (33554432u32, 527usize),
                    (536870908u32, 528usize),
                    (1476396101u32, 530usize),
                    (1979711489u32, 532usize),
                    (268435454u32, 535usize),
                    (268435422u32, 512usize),
                    (268435454u32, 519usize),
                    (268435454u32, 533usize),
                    (268435454u32, 536usize),
                    (268435454u32, 513usize),
                    (33554432u32, 279usize),
                    (33554432u32, 499usize),
                    (536870908u32, 500usize),
                    (33554432u32, 504usize),
                    (1476396101u32, 505usize),
                    (536870908u32, 526usize),
                    (33554432u32, 529usize),
                    (33554432u32, 530usize),
                    (1476396101u32, 531usize),
                    (1979711489u32, 533usize),
                    (268435454u32, 537usize),
                    (268435454u32, 527usize),
                    (268435454u32, 542usize),
                    (268435454u32, 544usize),
                    (268435454u32, 528usize),
                    (16777216u32, 241usize),
                    (16777216u32, 257usize),
                    (16777216u32, 322usize),
                    (16777216u32, 324usize),
                    (16777216u32, 338usize),
                    (1744831011u32, 354usize),
                    (1476396101u32, 355usize),
                    (16777216u32, 376usize),
                    (268435456u32, 379usize),
                    (134217727u32, 380usize),
                    (1744831011u32, 382usize),
                    (1476396101u32, 383usize),
                    (16777216u32, 443usize),
                    (536870908u32, 444usize),
                    (1744831011u32, 538usize),
                    (1476396101u32, 539usize),
                    (1996488705u32, 542usize),
                    (268435454u32, 545usize),
                    (268435454u32, 529usize),
                    (268435454u32, 543usize),
                    (268435454u32, 546usize),
                    (268435454u32, 526usize),
                    (16777216u32, 243usize),
                    (16777216u32, 259usize),
                    (16777216u32, 323usize),
                    (16777216u32, 325usize),
                    (16777216u32, 339usize),
                    (16777216u32, 354usize),
                    (33554432u32, 355usize),
                    (1744831011u32, 356usize),
                    (1476396101u32, 357usize),
                    (268435456u32, 374usize),
                    (134217727u32, 375usize),
                    (16777216u32, 381usize),
                    (16777216u32, 382usize),
                    (33554432u32, 383usize),
                    (1744831011u32, 384usize),
                    (1476396101u32, 385usize),
                    (536870908u32, 442usize),
                    (16777216u32, 445usize),
                    (16777216u32, 538usize),
                    (33554432u32, 539usize),
                    (1744831011u32, 540usize),
                    (1476396101u32, 541usize),
                    (1996488705u32, 543usize),
                    (268435454u32, 547usize),
                    (268435454u32, 554usize),
                    (268435454u32, 550usize),
                    (268435454u32, 556usize),
                    (268435454u32, 555usize),
                    (268435454u32, 551usize),
                    (268435454u32, 557usize),
                    (1048576u32, 443usize),
                    (536870912u32, 444usize),
                    (2012217345u32, 554usize),
                    (2004877313u32, 555usize),
                    (1048576u32, 276usize),
                    (1048576u32, 456usize),
                    (268435456u32, 457usize),
                    (1744830499u32, 458usize),
                    (1048576u32, 481usize),
                    (268435456u32, 482usize),
                    (1744830499u32, 484usize),
                    (1048576u32, 546usize),
                    (268435456u32, 547usize),
                    (1744830499u32, 548usize),
                    (2012217345u32, 550usize),
                    (2004877313u32, 551usize),
                    (268435454u32, 558usize),
                    (268435454u32, 559usize),
                    (268435454u32, 552usize),
                    (268435454u32, 561usize),
                    (268435454u32, 560usize),
                    (268435454u32, 553usize),
                    (268435454u32, 562usize),
                    (536870912u32, 442usize),
                    (1048576u32, 445usize),
                    (2012217345u32, 559usize),
                    (2004877313u32, 560usize),
                    (1048576u32, 277usize),
                    (1048576u32, 453usize),
                    (268435456u32, 454usize),
                    (1048576u32, 458usize),
                    (1744830499u32, 459usize),
                    (268435456u32, 480usize),
                    (1048576u32, 483usize),
                    (1048576u32, 484usize),
                    (1744830499u32, 485usize),
                    (1048576u32, 544usize),
                    (268435456u32, 545usize),
                    (1048576u32, 548usize),
                    (1744830499u32, 549usize),
                    (2012217345u32, 552usize),
                    (2004877313u32, 553usize),
                    (268435454u32, 563usize),
                    (268435454u32, 546usize),
                    (268435454u32, 568usize),
                    (268435454u32, 570usize),
                    (268435454u32, 547usize),
                    (16777216u32, 241usize),
                    (16777216u32, 257usize),
                    (16777216u32, 322usize),
                    (16777216u32, 324usize),
                    (16777216u32, 338usize),
                    (16777216u32, 340usize),
                    (1744831011u32, 354usize),
                    (1476396101u32, 355usize),
                    (16777216u32, 376usize),
                    (268435456u32, 379usize),
                    (134217727u32, 380usize),
                    (1744831011u32, 382usize),
                    (1476396101u32, 383usize),
                    (16777216u32, 443usize),
                    (536870908u32, 444usize),
                    (1744831011u32, 538usize),
                    (1476396101u32, 539usize),
                    (16777216u32, 558usize),
                    (268435456u32, 561usize),
                    (134217727u32, 562usize),
                    (1744831011u32, 564usize),
                    (1476396101u32, 565usize),
                    (1996488705u32, 568usize),
                    (268435454u32, 571usize),
                    (268435454u32, 544usize),
                    (268435454u32, 569usize),
                    (268435454u32, 572usize),
                    (268435454u32, 545usize),
                    (16777216u32, 243usize),
                    (16777216u32, 259usize),
                    (16777216u32, 323usize),
                    (16777216u32, 325usize),
                    (16777216u32, 339usize),
                    (16777216u32, 341usize),
                    (16777216u32, 354usize),
                    (33554432u32, 355usize),
                    (1744831011u32, 356usize),
                    (1476396101u32, 357usize),
                    (268435456u32, 374usize),
                    (134217727u32, 375usize),
                    (16777216u32, 381usize),
                    (16777216u32, 382usize),
                    (33554432u32, 383usize),
                    (1744831011u32, 384usize),
                    (1476396101u32, 385usize),
                    (536870908u32, 442usize),
                    (16777216u32, 445usize),
                    (16777216u32, 538usize),
                    (33554432u32, 539usize),
                    (1744831011u32, 540usize),
                    (1476396101u32, 541usize),
                    (268435456u32, 556usize),
                    (134217727u32, 557usize),
                    (16777216u32, 563usize),
                    (16777216u32, 564usize),
                    (33554432u32, 565usize),
                    (1744831011u32, 566usize),
                    (1476396101u32, 567usize),
                    (1996488705u32, 569usize),
                    (268435454u32, 573usize),
                    (268435454u32, 558usize),
                    (268435422u32, 561usize),
                    (268435454u32, 576usize),
                    (268435454u32, 578usize),
                    (268435454u32, 562usize),
                    (33554432u32, 276usize),
                    (33554432u32, 456usize),
                    (536870908u32, 457usize),
                    (1476396101u32, 458usize),
                    (33554432u32, 481usize),
                    (536870908u32, 482usize),
                    (1476396101u32, 484usize),
                    (33554432u32, 546usize),
                    (536870908u32, 547usize),
                    (1476396101u32, 548usize),
                    (33554432u32, 571usize),
                    (536870908u32, 572usize),
                    (1476396101u32, 574usize),
                    (1979711489u32, 576usize),
                    (268435454u32, 579usize),
                    (268435422u32, 556usize),
                    (268435454u32, 563usize),
                    (268435454u32, 577usize),
                    (268435454u32, 580usize),
                    (268435454u32, 557usize),
                    (33554432u32, 277usize),
                    (33554432u32, 453usize),
                    (536870908u32, 454usize),
                    (33554432u32, 458usize),
                    (1476396101u32, 459usize),
                    (536870908u32, 480usize),
                    (33554432u32, 483usize),
                    (33554432u32, 484usize),
                    (1476396101u32, 485usize),
                    (33554432u32, 544usize),
                    (536870908u32, 545usize),
                    (33554432u32, 548usize),
                    (1476396101u32, 549usize),
                    (536870908u32, 570usize),
                    (33554432u32, 573usize),
                    (33554432u32, 574usize),
                    (1476396101u32, 575usize),
                    (1979711489u32, 577usize),
                    (268435454u32, 581usize),
                    (268435454u32, 389usize),
                    (268435454u32, 586usize),
                    (268435454u32, 588usize),
                    (268435454u32, 390usize),
                    (16777216u32, 245usize),
                    (16777216u32, 261usize),
                    (16777216u32, 326usize),
                    (16777216u32, 328usize),
                    (16777216u32, 342usize),
                    (1744831011u32, 400usize),
                    (1476396101u32, 401usize),
                    (16777216u32, 422usize),
                    (268435456u32, 425usize),
                    (134217727u32, 426usize),
                    (1744831011u32, 428usize),
                    (1476396101u32, 429usize),
                    (16777216u32, 489usize),
                    (536870908u32, 490usize),
                    (1744831011u32, 582usize),
                    (1476396101u32, 583usize),
                    (1996488705u32, 586usize),
                    (268435454u32, 589usize),
                    (268435454u32, 391usize),
                    (268435454u32, 587usize),
                    (268435454u32, 590usize),
                    (268435454u32, 388usize),
                    (16777216u32, 247usize),
                    (16777216u32, 263usize),
                    (16777216u32, 327usize),
                    (16777216u32, 329usize),
                    (16777216u32, 343usize),
                    (16777216u32, 400usize),
                    (33554432u32, 401usize),
                    (1744831011u32, 402usize),
                    (1476396101u32, 403usize),
                    (268435456u32, 420usize),
                    (134217727u32, 421usize),
                    (16777216u32, 427usize),
                    (16777216u32, 428usize),
                    (33554432u32, 429usize),
                    (1744831011u32, 430usize),
                    (1476396101u32, 431usize),
                    (536870908u32, 488usize),
                    (16777216u32, 491usize),
                    (16777216u32, 582usize),
                    (33554432u32, 583usize),
                    (1744831011u32, 584usize),
                    (1476396101u32, 585usize),
                    (1996488705u32, 587usize),
                    (268435454u32, 591usize),
                    (268435454u32, 598usize),
                    (268435454u32, 594usize),
                    (268435454u32, 600usize),
                    (268435454u32, 599usize),
                    (268435454u32, 595usize),
                    (268435454u32, 601usize),
                    (1048576u32, 489usize),
                    (536870912u32, 490usize),
                    (2012217345u32, 598usize),
                    (2004877313u32, 599usize),
                    (1048576u32, 278usize),
                    (1048576u32, 502usize),
                    (268435456u32, 503usize),
                    (1744830499u32, 504usize),
                    (1048576u32, 527usize),
                    (268435456u32, 528usize),
                    (1744830499u32, 530usize),
                    (1048576u32, 590usize),
                    (268435456u32, 591usize),
                    (1744830499u32, 592usize),
                    (2012217345u32, 594usize),
                    (2004877313u32, 595usize),
                    (268435454u32, 602usize),
                    (268435454u32, 603usize),
                    (268435454u32, 596usize),
                    (268435454u32, 605usize),
                    (268435454u32, 604usize),
                    (268435454u32, 597usize),
                    (268435454u32, 606usize),
                    (536870912u32, 488usize),
                    (1048576u32, 491usize),
                    (2012217345u32, 603usize),
                    (2004877313u32, 604usize),
                    (1048576u32, 279usize),
                    (1048576u32, 499usize),
                    (268435456u32, 500usize),
                    (1048576u32, 504usize),
                    (1744830499u32, 505usize),
                    (268435456u32, 526usize),
                    (1048576u32, 529usize),
                    (1048576u32, 530usize),
                    (1744830499u32, 531usize),
                    (1048576u32, 588usize),
                    (268435456u32, 589usize),
                    (1048576u32, 592usize),
                    (1744830499u32, 593usize),
                    (2012217345u32, 596usize),
                    (2004877313u32, 597usize),
                    (268435454u32, 607usize),
                    (268435454u32, 590usize),
                    (268435454u32, 612usize),
                    (268435454u32, 614usize),
                    (268435454u32, 591usize),
                    (16777216u32, 245usize),
                    (16777216u32, 261usize),
                    (16777216u32, 326usize),
                    (16777216u32, 328usize),
                    (16777216u32, 342usize),
                    (16777216u32, 344usize),
                    (1744831011u32, 400usize),
                    (1476396101u32, 401usize),
                    (16777216u32, 422usize),
                    (268435456u32, 425usize),
                    (134217727u32, 426usize),
                    (1744831011u32, 428usize),
                    (1476396101u32, 429usize),
                    (16777216u32, 489usize),
                    (536870908u32, 490usize),
                    (1744831011u32, 582usize),
                    (1476396101u32, 583usize),
                    (16777216u32, 602usize),
                    (268435456u32, 605usize),
                    (134217727u32, 606usize),
                    (1744831011u32, 608usize),
                    (1476396101u32, 609usize),
                    (1996488705u32, 612usize),
                    (268435454u32, 615usize),
                    (268435454u32, 588usize),
                    (268435454u32, 613usize),
                    (268435454u32, 616usize),
                    (268435454u32, 589usize),
                    (16777216u32, 247usize),
                    (16777216u32, 263usize),
                    (16777216u32, 327usize),
                    (16777216u32, 329usize),
                    (16777216u32, 343usize),
                    (16777216u32, 345usize),
                    (16777216u32, 400usize),
                    (33554432u32, 401usize),
                    (1744831011u32, 402usize),
                    (1476396101u32, 403usize),
                    (268435456u32, 420usize),
                    (134217727u32, 421usize),
                    (16777216u32, 427usize),
                    (16777216u32, 428usize),
                    (33554432u32, 429usize),
                    (1744831011u32, 430usize),
                    (1476396101u32, 431usize),
                    (536870908u32, 488usize),
                    (16777216u32, 491usize),
                    (16777216u32, 582usize),
                    (33554432u32, 583usize),
                    (1744831011u32, 584usize),
                    (1476396101u32, 585usize),
                    (268435456u32, 600usize),
                    (134217727u32, 601usize),
                    (16777216u32, 607usize),
                    (16777216u32, 608usize),
                    (33554432u32, 609usize),
                    (1744831011u32, 610usize),
                    (1476396101u32, 611usize),
                    (1996488705u32, 613usize),
                    (268435454u32, 617usize),
                    (268435454u32, 602usize),
                    (268435422u32, 605usize),
                    (268435454u32, 620usize),
                    (268435454u32, 622usize),
                    (268435454u32, 606usize),
                    (33554432u32, 278usize),
                    (33554432u32, 502usize),
                    (536870908u32, 503usize),
                    (1476396101u32, 504usize),
                    (33554432u32, 527usize),
                    (536870908u32, 528usize),
                    (1476396101u32, 530usize),
                    (33554432u32, 590usize),
                    (536870908u32, 591usize),
                    (1476396101u32, 592usize),
                    (33554432u32, 615usize),
                    (536870908u32, 616usize),
                    (1476396101u32, 618usize),
                    (1979711489u32, 620usize),
                    (268435454u32, 623usize),
                    (268435422u32, 600usize),
                    (268435454u32, 607usize),
                    (268435454u32, 621usize),
                    (268435454u32, 624usize),
                    (268435454u32, 601usize),
                    (33554432u32, 279usize),
                    (33554432u32, 499usize),
                    (536870908u32, 500usize),
                    (33554432u32, 504usize),
                    (1476396101u32, 505usize),
                    (536870908u32, 526usize),
                    (33554432u32, 529usize),
                    (33554432u32, 530usize),
                    (1476396101u32, 531usize),
                    (33554432u32, 588usize),
                    (536870908u32, 589usize),
                    (33554432u32, 592usize),
                    (1476396101u32, 593usize),
                    (536870908u32, 614usize),
                    (33554432u32, 617usize),
                    (33554432u32, 618usize),
                    (1476396101u32, 619usize),
                    (1979711489u32, 621usize),
                    (268435454u32, 625usize),
                    (268435454u32, 435usize),
                    (268435454u32, 630usize),
                    (268435454u32, 632usize),
                    (268435454u32, 436usize),
                    (16777216u32, 249usize),
                    (16777216u32, 265usize),
                    (16777216u32, 330usize),
                    (16777216u32, 332usize),
                    (16777216u32, 346usize),
                    (1744831011u32, 446usize),
                    (1476396101u32, 447usize),
                    (16777216u32, 468usize),
                    (268435456u32, 471usize),
                    (134217727u32, 472usize),
                    (1744831011u32, 474usize),
                    (1476396101u32, 475usize),
                    (16777216u32, 535usize),
                    (536870908u32, 536usize),
                    (1744831011u32, 626usize),
                    (1476396101u32, 627usize),
                    (1996488705u32, 630usize),
                    (268435454u32, 633usize),
                    (268435454u32, 437usize),
                    (268435454u32, 631usize),
                    (268435454u32, 634usize),
                    (268435454u32, 434usize),
                    (16777216u32, 251usize),
                    (16777216u32, 267usize),
                    (16777216u32, 331usize),
                    (16777216u32, 333usize),
                    (16777216u32, 347usize),
                    (16777216u32, 446usize),
                    (33554432u32, 447usize),
                    (1744831011u32, 448usize),
                    (1476396101u32, 449usize),
                    (268435456u32, 466usize),
                    (134217727u32, 467usize),
                    (16777216u32, 473usize),
                    (16777216u32, 474usize),
                    (33554432u32, 475usize),
                    (1744831011u32, 476usize),
                    (1476396101u32, 477usize),
                    (536870908u32, 534usize),
                    (16777216u32, 537usize),
                    (16777216u32, 626usize),
                    (33554432u32, 627usize),
                    (1744831011u32, 628usize),
                    (1476396101u32, 629usize),
                    (1996488705u32, 631usize),
                    (268435454u32, 635usize),
                    (268435454u32, 642usize),
                    (268435454u32, 638usize),
                    (268435454u32, 644usize),
                    (268435454u32, 643usize),
                    (268435454u32, 639usize),
                    (268435454u32, 645usize),
                    (1048576u32, 535usize),
                    (536870912u32, 536usize),
                    (2012217345u32, 642usize),
                    (2004877313u32, 643usize),
                    (1048576u32, 272usize),
                    (1048576u32, 364usize),
                    (268435456u32, 365usize),
                    (1744830499u32, 366usize),
                    (1048576u32, 389usize),
                    (268435456u32, 390usize),
                    (1744830499u32, 392usize),
                    (1048576u32, 634usize),
                    (268435456u32, 635usize),
                    (1744830499u32, 636usize),
                    (2012217345u32, 638usize),
                    (2004877313u32, 639usize),
                    (268435454u32, 646usize),
                    (268435454u32, 647usize),
                    (268435454u32, 640usize),
                    (268435454u32, 649usize),
                    (268435454u32, 648usize),
                    (268435454u32, 641usize),
                    (268435454u32, 650usize),
                    (536870912u32, 534usize),
                    (1048576u32, 537usize),
                    (2012217345u32, 647usize),
                    (2004877313u32, 648usize),
                    (1048576u32, 273usize),
                    (1048576u32, 361usize),
                    (268435456u32, 362usize),
                    (1048576u32, 366usize),
                    (1744830499u32, 367usize),
                    (268435456u32, 388usize),
                    (1048576u32, 391usize),
                    (1048576u32, 392usize),
                    (1744830499u32, 393usize),
                    (1048576u32, 632usize),
                    (268435456u32, 633usize),
                    (1048576u32, 636usize),
                    (1744830499u32, 637usize),
                    (2012217345u32, 640usize),
                    (2004877313u32, 641usize),
                    (268435454u32, 651usize),
                    (268435454u32, 634usize),
                    (268435454u32, 656usize),
                    (268435454u32, 658usize),
                    (268435454u32, 635usize),
                    (16777216u32, 249usize),
                    (16777216u32, 265usize),
                    (16777216u32, 330usize),
                    (16777216u32, 332usize),
                    (16777216u32, 346usize),
                    (16777216u32, 348usize),
                    (1744831011u32, 446usize),
                    (1476396101u32, 447usize),
                    (16777216u32, 468usize),
                    (268435456u32, 471usize),
                    (134217727u32, 472usize),
                    (1744831011u32, 474usize),
                    (1476396101u32, 475usize),
                    (16777216u32, 535usize),
                    (536870908u32, 536usize),
                    (1744831011u32, 626usize),
                    (1476396101u32, 627usize),
                    (16777216u32, 646usize),
                    (268435456u32, 649usize),
                    (134217727u32, 650usize),
                    (1744831011u32, 652usize),
                    (1476396101u32, 653usize),
                    (1996488705u32, 656usize),
                    (268435454u32, 659usize),
                    (268435454u32, 632usize),
                    (268435454u32, 657usize),
                    (268435454u32, 660usize),
                    (268435454u32, 633usize),
                    (16777216u32, 251usize),
                    (16777216u32, 267usize),
                    (16777216u32, 331usize),
                    (16777216u32, 333usize),
                    (16777216u32, 347usize),
                    (16777216u32, 349usize),
                    (16777216u32, 446usize),
                    (33554432u32, 447usize),
                    (1744831011u32, 448usize),
                    (1476396101u32, 449usize),
                    (268435456u32, 466usize),
                    (134217727u32, 467usize),
                    (16777216u32, 473usize),
                    (16777216u32, 474usize),
                    (33554432u32, 475usize),
                    (1744831011u32, 476usize),
                    (1476396101u32, 477usize),
                    (536870908u32, 534usize),
                    (16777216u32, 537usize),
                    (16777216u32, 626usize),
                    (33554432u32, 627usize),
                    (1744831011u32, 628usize),
                    (1476396101u32, 629usize),
                    (268435456u32, 644usize),
                    (134217727u32, 645usize),
                    (16777216u32, 651usize),
                    (16777216u32, 652usize),
                    (33554432u32, 653usize),
                    (1744831011u32, 654usize),
                    (1476396101u32, 655usize),
                    (1996488705u32, 657usize),
                    (268435454u32, 661usize),
                    (268435454u32, 646usize),
                    (268435422u32, 649usize),
                    (268435454u32, 664usize),
                    (268435454u32, 666usize),
                    (268435454u32, 650usize),
                    (33554432u32, 272usize),
                    (33554432u32, 364usize),
                    (536870908u32, 365usize),
                    (1476396101u32, 366usize),
                    (33554432u32, 389usize),
                    (536870908u32, 390usize),
                    (1476396101u32, 392usize),
                    (33554432u32, 634usize),
                    (536870908u32, 635usize),
                    (1476396101u32, 636usize),
                    (33554432u32, 659usize),
                    (536870908u32, 660usize),
                    (1476396101u32, 662usize),
                    (1979711489u32, 664usize),
                    (268435454u32, 667usize),
                    (268435422u32, 644usize),
                    (268435454u32, 651usize),
                    (268435454u32, 665usize),
                    (268435454u32, 668usize),
                    (268435454u32, 645usize),
                    (33554432u32, 273usize),
                    (33554432u32, 361usize),
                    (536870908u32, 362usize),
                    (33554432u32, 366usize),
                    (1476396101u32, 367usize),
                    (536870908u32, 388usize),
                    (33554432u32, 391usize),
                    (33554432u32, 392usize),
                    (1476396101u32, 393usize),
                    (33554432u32, 632usize),
                    (536870908u32, 633usize),
                    (33554432u32, 636usize),
                    (1476396101u32, 637usize),
                    (536870908u32, 658usize),
                    (33554432u32, 661usize),
                    (33554432u32, 662usize),
                    (1476396101u32, 663usize),
                    (1979711489u32, 665usize),
                    (268435454u32, 669usize),
                    (268435454u32, 481usize),
                    (268435454u32, 674usize),
                    (268435454u32, 676usize),
                    (268435454u32, 482usize),
                    (16777216u32, 253usize),
                    (16777216u32, 269usize),
                    (16777216u32, 334usize),
                    (16777216u32, 336usize),
                    (16777216u32, 350usize),
                    (16777216u32, 397usize),
                    (536870908u32, 398usize),
                    (1744831011u32, 492usize),
                    (1476396101u32, 493usize),
                    (16777216u32, 514usize),
                    (268435456u32, 517usize),
                    (134217727u32, 518usize),
                    (1744831011u32, 520usize),
                    (1476396101u32, 521usize),
                    (1744831011u32, 670usize),
                    (1476396101u32, 671usize),
                    (1996488705u32, 674usize),
                    (268435454u32, 677usize),
                    (268435454u32, 483usize),
                    (268435454u32, 675usize),
                    (268435454u32, 678usize),
                    (268435454u32, 480usize),
                    (16777216u32, 255usize),
                    (16777216u32, 271usize),
                    (16777216u32, 335usize),
                    (16777216u32, 337usize),
                    (16777216u32, 351usize),
                    (536870908u32, 396usize),
                    (16777216u32, 399usize),
                    (16777216u32, 492usize),
                    (33554432u32, 493usize),
                    (1744831011u32, 494usize),
                    (1476396101u32, 495usize),
                    (268435456u32, 512usize),
                    (134217727u32, 513usize),
                    (16777216u32, 519usize),
                    (16777216u32, 520usize),
                    (33554432u32, 521usize),
                    (1744831011u32, 522usize),
                    (1476396101u32, 523usize),
                    (16777216u32, 670usize),
                    (33554432u32, 671usize),
                    (1744831011u32, 672usize),
                    (1476396101u32, 673usize),
                    (1996488705u32, 675usize),
                    (268435454u32, 679usize),
                    (268435454u32, 686usize),
                    (268435454u32, 682usize),
                    (268435454u32, 688usize),
                    (268435454u32, 687usize),
                    (268435454u32, 683usize),
                    (268435454u32, 689usize),
                    (1048576u32, 397usize),
                    (536870912u32, 398usize),
                    (2012217345u32, 686usize),
                    (2004877313u32, 687usize),
                    (1048576u32, 274usize),
                    (1048576u32, 410usize),
                    (268435456u32, 411usize),
                    (1744830499u32, 412usize),
                    (1048576u32, 435usize),
                    (268435456u32, 436usize),
                    (1744830499u32, 438usize),
                    (1048576u32, 678usize),
                    (268435456u32, 679usize),
                    (1744830499u32, 680usize),
                    (2012217345u32, 682usize),
                    (2004877313u32, 683usize),
                    (268435454u32, 690usize),
                    (268435454u32, 691usize),
                    (268435454u32, 684usize),
                    (268435454u32, 693usize),
                    (268435454u32, 692usize),
                    (268435454u32, 685usize),
                    (268435454u32, 694usize),
                    (536870912u32, 396usize),
                    (1048576u32, 399usize),
                    (2012217345u32, 691usize),
                    (2004877313u32, 692usize),
                    (1048576u32, 275usize),
                    (1048576u32, 407usize),
                    (268435456u32, 408usize),
                    (1048576u32, 412usize),
                    (1744830499u32, 413usize),
                    (268435456u32, 434usize),
                    (1048576u32, 437usize),
                    (1048576u32, 438usize),
                    (1744830499u32, 439usize),
                    (1048576u32, 676usize),
                    (268435456u32, 677usize),
                    (1048576u32, 680usize),
                    (1744830499u32, 681usize),
                    (2012217345u32, 684usize),
                    (2004877313u32, 685usize),
                    (268435454u32, 695usize),
                    (268435454u32, 678usize),
                    (268435454u32, 700usize),
                    (268435454u32, 702usize),
                    (268435454u32, 679usize),
                    (16777216u32, 253usize),
                    (16777216u32, 269usize),
                    (16777216u32, 334usize),
                    (16777216u32, 336usize),
                    (16777216u32, 350usize),
                    (16777216u32, 352usize),
                    (16777216u32, 397usize),
                    (536870908u32, 398usize),
                    (1744831011u32, 492usize),
                    (1476396101u32, 493usize),
                    (16777216u32, 514usize),
                    (268435456u32, 517usize),
                    (134217727u32, 518usize),
                    (1744831011u32, 520usize),
                    (1476396101u32, 521usize),
                    (1744831011u32, 670usize),
                    (1476396101u32, 671usize),
                    (16777216u32, 690usize),
                    (268435456u32, 693usize),
                    (134217727u32, 694usize),
                    (1744831011u32, 696usize),
                    (1476396101u32, 697usize),
                    (1996488705u32, 700usize),
                    (268435454u32, 703usize),
                    (268435454u32, 676usize),
                    (268435454u32, 701usize),
                    (268435454u32, 704usize),
                    (268435454u32, 677usize),
                    (16777216u32, 255usize),
                    (16777216u32, 271usize),
                    (16777216u32, 335usize),
                    (16777216u32, 337usize),
                    (16777216u32, 351usize),
                    (16777216u32, 353usize),
                    (536870908u32, 396usize),
                    (16777216u32, 399usize),
                    (16777216u32, 492usize),
                    (33554432u32, 493usize),
                    (1744831011u32, 494usize),
                    (1476396101u32, 495usize),
                    (268435456u32, 512usize),
                    (134217727u32, 513usize),
                    (16777216u32, 519usize),
                    (16777216u32, 520usize),
                    (33554432u32, 521usize),
                    (1744831011u32, 522usize),
                    (1476396101u32, 523usize),
                    (16777216u32, 670usize),
                    (33554432u32, 671usize),
                    (1744831011u32, 672usize),
                    (1476396101u32, 673usize),
                    (268435456u32, 688usize),
                    (134217727u32, 689usize),
                    (16777216u32, 695usize),
                    (16777216u32, 696usize),
                    (33554432u32, 697usize),
                    (1744831011u32, 698usize),
                    (1476396101u32, 699usize),
                    (1996488705u32, 701usize),
                    (268435454u32, 705usize),
                    (268435454u32, 690usize),
                    (268435422u32, 693usize),
                    (268435454u32, 708usize),
                    (268435454u32, 710usize),
                    (268435454u32, 694usize),
                    (33554432u32, 274usize),
                    (33554432u32, 410usize),
                    (536870908u32, 411usize),
                    (1476396101u32, 412usize),
                    (33554432u32, 435usize),
                    (536870908u32, 436usize),
                    (1476396101u32, 438usize),
                    (33554432u32, 678usize),
                    (536870908u32, 679usize),
                    (1476396101u32, 680usize),
                    (33554432u32, 703usize),
                    (536870908u32, 704usize),
                    (1476396101u32, 706usize),
                    (1979711489u32, 708usize),
                    (268435454u32, 711usize),
                    (268435422u32, 688usize),
                    (268435454u32, 695usize),
                    (268435454u32, 709usize),
                    (268435454u32, 712usize),
                    (268435454u32, 689usize),
                    (33554432u32, 275usize),
                    (33554432u32, 407usize),
                    (536870908u32, 408usize),
                    (33554432u32, 412usize),
                    (1476396101u32, 413usize),
                    (536870908u32, 434usize),
                    (33554432u32, 437usize),
                    (33554432u32, 438usize),
                    (1476396101u32, 439usize),
                    (33554432u32, 676usize),
                    (536870908u32, 677usize),
                    (33554432u32, 680usize),
                    (1476396101u32, 681usize),
                    (536870908u32, 702usize),
                    (33554432u32, 705usize),
                    (33554432u32, 706usize),
                    (1476396101u32, 707usize),
                    (1979711489u32, 709usize),
                    (268435454u32, 713usize),
                    (268435454u32, 714usize),
                    (268435454u32, 664usize),
                    (268435454u32, 715usize),
                    (33554432u32, 240usize),
                    (1979711489u32, 714usize),
                    (33554432u32, 272usize),
                    (33554432u32, 364usize),
                    (536870908u32, 365usize),
                    (1476396101u32, 366usize),
                    (33554432u32, 389usize),
                    (536870908u32, 390usize),
                    (1476396101u32, 392usize),
                    (33554432u32, 634usize),
                    (536870908u32, 635usize),
                    (1476396101u32, 636usize),
                    (33554432u32, 659usize),
                    (536870908u32, 660usize),
                    (1476396101u32, 662usize),
                    (1979711489u32, 664usize),
                    (268435454u32, 716usize),
                    (268435454u32, 715usize),
                    (268435454u32, 717usize),
                    (268435454u32, 719usize),
                    (268435454u32, 716usize),
                    (33554432u32, 241usize),
                    (33554432u32, 257usize),
                    (33554432u32, 322usize),
                    (33554432u32, 324usize),
                    (33554432u32, 338usize),
                    (33554432u32, 340usize),
                    (1476396101u32, 354usize),
                    (939526281u32, 355usize),
                    (33554432u32, 376usize),
                    (536870912u32, 379usize),
                    (268435454u32, 380usize),
                    (1476396101u32, 382usize),
                    (939526281u32, 383usize),
                    (33554432u32, 443usize),
                    (1073741816u32, 444usize),
                    (1476396101u32, 538usize),
                    (939526281u32, 539usize),
                    (33554432u32, 558usize),
                    (536870912u32, 561usize),
                    (268435454u32, 562usize),
                    (1476396101u32, 564usize),
                    (939526281u32, 565usize),
                    (1979711489u32, 568usize),
                    (268435454u32, 718usize),
                    (268435454u32, 720usize),
                    (268435454u32, 721usize),
                    (268435454u32, 665usize),
                    (268435454u32, 722usize),
                    (33554432u32, 242usize),
                    (1979711489u32, 721usize),
                    (33554432u32, 273usize),
                    (33554432u32, 361usize),
                    (536870908u32, 362usize),
                    (33554432u32, 366usize),
                    (1476396101u32, 367usize),
                    (536870908u32, 388usize),
                    (33554432u32, 391usize),
                    (33554432u32, 392usize),
                    (1476396101u32, 393usize),
                    (33554432u32, 632usize),
                    (536870908u32, 633usize),
                    (33554432u32, 636usize),
                    (1476396101u32, 637usize),
                    (536870908u32, 658usize),
                    (33554432u32, 661usize),
                    (33554432u32, 662usize),
                    (1476396101u32, 663usize),
                    (1979711489u32, 665usize),
                    (268435454u32, 723usize),
                    (268435454u32, 722usize),
                    (268435454u32, 724usize),
                    (268435454u32, 726usize),
                    (268435454u32, 723usize),
                    (33554432u32, 243usize),
                    (33554432u32, 259usize),
                    (33554432u32, 323usize),
                    (33554432u32, 325usize),
                    (33554432u32, 339usize),
                    (33554432u32, 341usize),
                    (33554432u32, 354usize),
                    (67108864u32, 355usize),
                    (1476396101u32, 356usize),
                    (939526281u32, 357usize),
                    (536870912u32, 374usize),
                    (268435454u32, 375usize),
                    (33554432u32, 381usize),
                    (33554432u32, 382usize),
                    (67108864u32, 383usize),
                    (1476396101u32, 384usize),
                    (939526281u32, 385usize),
                    (1073741816u32, 442usize),
                    (33554432u32, 445usize),
                    (33554432u32, 538usize),
                    (67108864u32, 539usize),
                    (1476396101u32, 540usize),
                    (939526281u32, 541usize),
                    (536870912u32, 556usize),
                    (268435454u32, 557usize),
                    (33554432u32, 563usize),
                    (33554432u32, 564usize),
                    (67108864u32, 565usize),
                    (1476396101u32, 566usize),
                    (939526281u32, 567usize),
                    (1979711489u32, 569usize),
                    (268435454u32, 725usize),
                    (268435454u32, 727usize),
                    (268435454u32, 728usize),
                    (268435454u32, 708usize),
                    (268435454u32, 729usize),
                    (33554432u32, 244usize),
                    (1979711489u32, 728usize),
                    (33554432u32, 274usize),
                    (33554432u32, 410usize),
                    (536870908u32, 411usize),
                    (1476396101u32, 412usize),
                    (33554432u32, 435usize),
                    (536870908u32, 436usize),
                    (1476396101u32, 438usize),
                    (33554432u32, 678usize),
                    (536870908u32, 679usize),
                    (1476396101u32, 680usize),
                    (33554432u32, 703usize),
                    (536870908u32, 704usize),
                    (1476396101u32, 706usize),
                    (1979711489u32, 708usize),
                    (268435454u32, 730usize),
                    (268435454u32, 729usize),
                    (268435454u32, 731usize),
                    (268435454u32, 733usize),
                    (268435454u32, 730usize),
                    (33554432u32, 245usize),
                    (33554432u32, 261usize),
                    (33554432u32, 326usize),
                    (33554432u32, 328usize),
                    (33554432u32, 342usize),
                    (33554432u32, 344usize),
                    (1476396101u32, 400usize),
                    (939526281u32, 401usize),
                    (33554432u32, 422usize),
                    (536870912u32, 425usize),
                    (268435454u32, 426usize),
                    (1476396101u32, 428usize),
                    (939526281u32, 429usize),
                    (33554432u32, 489usize),
                    (1073741816u32, 490usize),
                    (1476396101u32, 582usize),
                    (939526281u32, 583usize),
                    (33554432u32, 602usize),
                    (536870912u32, 605usize),
                    (268435454u32, 606usize),
                    (1476396101u32, 608usize),
                    (939526281u32, 609usize),
                    (1979711489u32, 612usize),
                    (268435454u32, 732usize),
                    (268435454u32, 734usize),
                    (268435454u32, 735usize),
                    (268435454u32, 709usize),
                    (268435454u32, 736usize),
                    (33554432u32, 246usize),
                    (1979711489u32, 735usize),
                    (33554432u32, 275usize),
                    (33554432u32, 407usize),
                    (536870908u32, 408usize),
                    (33554432u32, 412usize),
                    (1476396101u32, 413usize),
                    (536870908u32, 434usize),
                    (33554432u32, 437usize),
                    (33554432u32, 438usize),
                    (1476396101u32, 439usize),
                    (33554432u32, 676usize),
                    (536870908u32, 677usize),
                    (33554432u32, 680usize),
                    (1476396101u32, 681usize),
                    (536870908u32, 702usize),
                    (33554432u32, 705usize),
                    (33554432u32, 706usize),
                    (1476396101u32, 707usize),
                    (1979711489u32, 709usize),
                    (268435454u32, 737usize),
                    (268435454u32, 736usize),
                    (268435454u32, 738usize),
                    (268435454u32, 740usize),
                    (268435454u32, 737usize),
                    (33554432u32, 247usize),
                    (33554432u32, 263usize),
                    (33554432u32, 327usize),
                    (33554432u32, 329usize),
                    (33554432u32, 343usize),
                    (33554432u32, 345usize),
                    (33554432u32, 400usize),
                    (67108864u32, 401usize),
                    (1476396101u32, 402usize),
                    (939526281u32, 403usize),
                    (536870912u32, 420usize),
                    (268435454u32, 421usize),
                    (33554432u32, 427usize),
                    (33554432u32, 428usize),
                    (67108864u32, 429usize),
                    (1476396101u32, 430usize),
                    (939526281u32, 431usize),
                    (1073741816u32, 488usize),
                    (33554432u32, 491usize),
                    (33554432u32, 582usize),
                    (67108864u32, 583usize),
                    (1476396101u32, 584usize),
                    (939526281u32, 585usize),
                    (536870912u32, 600usize),
                    (268435454u32, 601usize),
                    (33554432u32, 607usize),
                    (33554432u32, 608usize),
                    (67108864u32, 609usize),
                    (1476396101u32, 610usize),
                    (939526281u32, 611usize),
                    (1979711489u32, 613usize),
                    (268435454u32, 739usize),
                    (268435454u32, 741usize),
                    (268435454u32, 742usize),
                    (268435454u32, 576usize),
                    (268435454u32, 743usize),
                    (33554432u32, 248usize),
                    (1979711489u32, 742usize),
                    (33554432u32, 276usize),
                    (33554432u32, 456usize),
                    (536870908u32, 457usize),
                    (1476396101u32, 458usize),
                    (33554432u32, 481usize),
                    (536870908u32, 482usize),
                    (1476396101u32, 484usize),
                    (33554432u32, 546usize),
                    (536870908u32, 547usize),
                    (1476396101u32, 548usize),
                    (33554432u32, 571usize),
                    (536870908u32, 572usize),
                    (1476396101u32, 574usize),
                    (1979711489u32, 576usize),
                    (268435454u32, 744usize),
                    (268435454u32, 743usize),
                    (268435454u32, 745usize),
                    (268435454u32, 747usize),
                    (268435454u32, 744usize),
                    (33554432u32, 249usize),
                    (33554432u32, 265usize),
                    (33554432u32, 330usize),
                    (33554432u32, 332usize),
                    (33554432u32, 346usize),
                    (33554432u32, 348usize),
                    (1476396101u32, 446usize),
                    (939526281u32, 447usize),
                    (33554432u32, 468usize),
                    (536870912u32, 471usize),
                    (268435454u32, 472usize),
                    (1476396101u32, 474usize),
                    (939526281u32, 475usize),
                    (33554432u32, 535usize),
                    (1073741816u32, 536usize),
                    (1476396101u32, 626usize),
                    (939526281u32, 627usize),
                    (33554432u32, 646usize),
                    (536870912u32, 649usize),
                    (268435454u32, 650usize),
                    (1476396101u32, 652usize),
                    (939526281u32, 653usize),
                    (1979711489u32, 656usize),
                    (268435454u32, 746usize),
                    (268435454u32, 748usize),
                    (268435454u32, 749usize),
                    (268435454u32, 577usize),
                    (268435454u32, 750usize),
                    (33554432u32, 250usize),
                    (1979711489u32, 749usize),
                    (33554432u32, 277usize),
                    (33554432u32, 453usize),
                    (536870908u32, 454usize),
                    (33554432u32, 458usize),
                    (1476396101u32, 459usize),
                    (536870908u32, 480usize),
                    (33554432u32, 483usize),
                    (33554432u32, 484usize),
                    (1476396101u32, 485usize),
                    (33554432u32, 544usize),
                    (536870908u32, 545usize),
                    (33554432u32, 548usize),
                    (1476396101u32, 549usize),
                    (536870908u32, 570usize),
                    (33554432u32, 573usize),
                    (33554432u32, 574usize),
                    (1476396101u32, 575usize),
                    (1979711489u32, 577usize),
                    (268435454u32, 751usize),
                    (268435454u32, 750usize),
                    (268435454u32, 752usize),
                    (268435454u32, 754usize),
                    (268435454u32, 751usize),
                    (33554432u32, 251usize),
                    (33554432u32, 267usize),
                    (33554432u32, 331usize),
                    (33554432u32, 333usize),
                    (33554432u32, 347usize),
                    (33554432u32, 349usize),
                    (33554432u32, 446usize),
                    (67108864u32, 447usize),
                    (1476396101u32, 448usize),
                    (939526281u32, 449usize),
                    (536870912u32, 466usize),
                    (268435454u32, 467usize),
                    (33554432u32, 473usize),
                    (33554432u32, 474usize),
                    (67108864u32, 475usize),
                    (1476396101u32, 476usize),
                    (939526281u32, 477usize),
                    (1073741816u32, 534usize),
                    (33554432u32, 537usize),
                    (33554432u32, 626usize),
                    (67108864u32, 627usize),
                    (1476396101u32, 628usize),
                    (939526281u32, 629usize),
                    (536870912u32, 644usize),
                    (268435454u32, 645usize),
                    (33554432u32, 651usize),
                    (33554432u32, 652usize),
                    (67108864u32, 653usize),
                    (1476396101u32, 654usize),
                    (939526281u32, 655usize),
                    (1979711489u32, 657usize),
                    (268435454u32, 753usize),
                    (268435454u32, 755usize),
                    (268435454u32, 756usize),
                    (268435454u32, 620usize),
                    (268435454u32, 757usize),
                    (33554432u32, 252usize),
                    (1979711489u32, 756usize),
                    (33554432u32, 278usize),
                    (33554432u32, 502usize),
                    (536870908u32, 503usize),
                    (1476396101u32, 504usize),
                    (33554432u32, 527usize),
                    (536870908u32, 528usize),
                    (1476396101u32, 530usize),
                    (33554432u32, 590usize),
                    (536870908u32, 591usize),
                    (1476396101u32, 592usize),
                    (33554432u32, 615usize),
                    (536870908u32, 616usize),
                    (1476396101u32, 618usize),
                    (1979711489u32, 620usize),
                    (268435454u32, 758usize),
                    (268435454u32, 757usize),
                    (268435454u32, 759usize),
                    (268435454u32, 761usize),
                    (268435454u32, 758usize),
                    (33554432u32, 253usize),
                    (33554432u32, 269usize),
                    (33554432u32, 334usize),
                    (33554432u32, 336usize),
                    (33554432u32, 350usize),
                    (33554432u32, 352usize),
                    (33554432u32, 397usize),
                    (1073741816u32, 398usize),
                    (1476396101u32, 492usize),
                    (939526281u32, 493usize),
                    (33554432u32, 514usize),
                    (536870912u32, 517usize),
                    (268435454u32, 518usize),
                    (1476396101u32, 520usize),
                    (939526281u32, 521usize),
                    (1476396101u32, 670usize),
                    (939526281u32, 671usize),
                    (33554432u32, 690usize),
                    (536870912u32, 693usize),
                    (268435454u32, 694usize),
                    (1476396101u32, 696usize),
                    (939526281u32, 697usize),
                    (1979711489u32, 700usize),
                    (268435454u32, 760usize),
                    (268435454u32, 762usize),
                    (268435454u32, 763usize),
                    (268435454u32, 621usize),
                    (268435454u32, 764usize),
                    (33554432u32, 254usize),
                    (1979711489u32, 763usize),
                    (33554432u32, 279usize),
                    (33554432u32, 499usize),
                    (536870908u32, 500usize),
                    (33554432u32, 504usize),
                    (1476396101u32, 505usize),
                    (536870908u32, 526usize),
                    (33554432u32, 529usize),
                    (33554432u32, 530usize),
                    (1476396101u32, 531usize),
                    (33554432u32, 588usize),
                    (536870908u32, 589usize),
                    (33554432u32, 592usize),
                    (1476396101u32, 593usize),
                    (536870908u32, 614usize),
                    (33554432u32, 617usize),
                    (33554432u32, 618usize),
                    (1476396101u32, 619usize),
                    (1979711489u32, 621usize),
                    (268435454u32, 765usize),
                    (268435454u32, 764usize),
                    (268435454u32, 766usize),
                    (268435454u32, 768usize),
                    (268435454u32, 765usize),
                    (33554432u32, 255usize),
                    (33554432u32, 271usize),
                    (33554432u32, 335usize),
                    (33554432u32, 337usize),
                    (33554432u32, 351usize),
                    (33554432u32, 353usize),
                    (1073741816u32, 396usize),
                    (33554432u32, 399usize),
                    (33554432u32, 492usize),
                    (67108864u32, 493usize),
                    (1476396101u32, 494usize),
                    (939526281u32, 495usize),
                    (536870912u32, 512usize),
                    (268435454u32, 513usize),
                    (33554432u32, 519usize),
                    (33554432u32, 520usize),
                    (67108864u32, 521usize),
                    (1476396101u32, 522usize),
                    (939526281u32, 523usize),
                    (33554432u32, 670usize),
                    (67108864u32, 671usize),
                    (1476396101u32, 672usize),
                    (939526281u32, 673usize),
                    (536870912u32, 688usize),
                    (268435454u32, 689usize),
                    (33554432u32, 695usize),
                    (33554432u32, 696usize),
                    (67108864u32, 697usize),
                    (1476396101u32, 698usize),
                    (939526281u32, 699usize),
                    (1979711489u32, 701usize),
                    (268435454u32, 767usize),
                    (268435454u32, 769usize),
                    (268435454u32, 711usize),
                    (268435454u32, 770usize),
                    (268435454u32, 771usize),
                    (268435454u32, 712usize),
                    (8388608u32, 256usize),
                    (2004877313u32, 770usize),
                    (268435454u32, 772usize),
                    (268435454u32, 615usize),
                    (268435454u32, 773usize),
                    (268435454u32, 775usize),
                    (268435454u32, 616usize),
                    (536870908u32, 772usize),
                    (268435454u32, 774usize),
                    (268435454u32, 776usize),
                    (268435454u32, 713usize),
                    (268435454u32, 777usize),
                    (268435454u32, 778usize),
                    (268435454u32, 710usize),
                    (8388608u32, 258usize),
                    (2004877313u32, 777usize),
                    (268435454u32, 779usize),
                    (268435454u32, 617usize),
                    (268435454u32, 780usize),
                    (268435454u32, 782usize),
                    (268435454u32, 614usize),
                    (536870908u32, 779usize),
                    (268435454u32, 781usize),
                    (268435454u32, 783usize),
                    (268435454u32, 579usize),
                    (268435454u32, 784usize),
                    (268435454u32, 785usize),
                    (268435454u32, 580usize),
                    (8388608u32, 260usize),
                    (2004877313u32, 784usize),
                    (268435454u32, 786usize),
                    (268435454u32, 659usize),
                    (268435454u32, 787usize),
                    (268435454u32, 789usize),
                    (268435454u32, 660usize),
                    (536870908u32, 786usize),
                    (268435454u32, 788usize),
                    (268435454u32, 790usize),
                    (268435454u32, 581usize),
                    (268435454u32, 791usize),
                    (268435454u32, 792usize),
                    (268435454u32, 578usize),
                    (8388608u32, 262usize),
                    (2004877313u32, 791usize),
                    (268435454u32, 793usize),
                    (268435454u32, 661usize),
                    (268435454u32, 794usize),
                    (268435454u32, 796usize),
                    (268435454u32, 658usize),
                    (536870908u32, 793usize),
                    (268435454u32, 795usize),
                    (268435454u32, 797usize),
                    (268435454u32, 623usize),
                    (268435454u32, 798usize),
                    (268435454u32, 799usize),
                    (268435454u32, 624usize),
                    (8388608u32, 264usize),
                    (2004877313u32, 798usize),
                    (268435454u32, 800usize),
                    (268435454u32, 703usize),
                    (268435454u32, 801usize),
                    (268435454u32, 803usize),
                    (268435454u32, 704usize),
                    (536870908u32, 800usize),
                    (268435454u32, 802usize),
                    (268435454u32, 804usize),
                    (268435454u32, 625usize),
                    (268435454u32, 805usize),
                    (268435454u32, 806usize),
                    (268435454u32, 622usize),
                    (8388608u32, 266usize),
                    (2004877313u32, 805usize),
                    (268435454u32, 807usize),
                    (268435454u32, 705usize),
                    (268435454u32, 808usize),
                    (268435454u32, 810usize),
                    (268435454u32, 702usize),
                    (536870908u32, 807usize),
                    (268435454u32, 809usize),
                    (268435454u32, 811usize),
                    (268435454u32, 667usize),
                    (268435454u32, 812usize),
                    (268435454u32, 813usize),
                    (268435454u32, 668usize),
                    (8388608u32, 268usize),
                    (2004877313u32, 812usize),
                    (268435454u32, 814usize),
                    (268435454u32, 571usize),
                    (268435454u32, 815usize),
                    (268435454u32, 817usize),
                    (268435454u32, 572usize),
                    (536870908u32, 814usize),
                    (268435454u32, 816usize),
                    (268435454u32, 818usize),
                    (268435454u32, 669usize),
                    (268435454u32, 819usize),
                    (268435454u32, 820usize),
                    (268435454u32, 666usize),
                    (8388608u32, 270usize),
                    (2004877313u32, 819usize),
                    (268435454u32, 821usize),
                    (268435454u32, 573usize),
                    (268435454u32, 822usize),
                    (268435454u32, 824usize),
                ];
                let mut _vl = 0;
                while _vl < 207usize {
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
                const VS_DESCS: [(usize, usize, usize); 1usize] = [(1051usize, 0usize, 4usize)];
                const VS_DEPS: [usize; 4usize] = [871usize, 872usize, 873usize, 874usize];
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
