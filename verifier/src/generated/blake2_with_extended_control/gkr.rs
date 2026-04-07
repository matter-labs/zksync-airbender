use super::common::{
    dot_eq, draw_field_els_into, fold_standard_claims, make_eq_poly, read_field_el,
    read_reduced_field_el, verify_final_step_check, verify_sumcheck_rounds, EXT_DEGREE,
};
use super::constants::*;
use verifier_common::blake2s_u32::DelegatedBlake2sState;
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::field::{Field, FieldExtension, PrimeField};
use verifier_common::field_ops;
use verifier_common::gkr::{GKRVerificationError, GKRVerifierOutput, LayerState, LazyVec};
use verifier_common::non_determinism_source::NonDeterminismSource;
use verifier_common::structs::CommitBuf;
use verifier_common::transcript::Blake2sTranscript;
#[inline(always)]
#[allow(clippy::needless_borrow)]
unsafe fn layer_0_compute_claim(
    output_claims: &LazyVec<BabyBearExt4, GKR_ADDRS>,
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    const DESCS: [(usize, usize, usize); 196usize] = [
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
    ];
    let mut combined = BabyBearExt4::ZERO;
    let mut current_batch = BabyBearExt4::ONE;
    let mut i = 0;
    while i < 196usize {
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
        const SIMPLE_GATES: [(usize, [usize; 4]); 194usize] = [
            (1usize, [626usize, 0usize, 0usize, 0usize]),
            (2usize, [630usize, 631usize, 0usize, 0usize]),
            (2usize, [632usize, 633usize, 0usize, 0usize]),
            (2usize, [634usize, 635usize, 0usize, 0usize]),
            (2usize, [636usize, 637usize, 0usize, 0usize]),
            (2usize, [638usize, 639usize, 0usize, 0usize]),
            (2usize, [640usize, 641usize, 0usize, 0usize]),
            (2usize, [642usize, 643usize, 0usize, 0usize]),
            (2usize, [644usize, 645usize, 0usize, 0usize]),
            (2usize, [646usize, 647usize, 0usize, 0usize]),
            (2usize, [648usize, 649usize, 0usize, 0usize]),
            (2usize, [650usize, 651usize, 0usize, 0usize]),
            (2usize, [652usize, 653usize, 0usize, 0usize]),
            (2usize, [654usize, 655usize, 0usize, 0usize]),
            (2usize, [656usize, 657usize, 0usize, 0usize]),
            (2usize, [658usize, 659usize, 0usize, 0usize]),
            (2usize, [660usize, 661usize, 0usize, 0usize]),
            (2usize, [662usize, 663usize, 0usize, 0usize]),
            (2usize, [664usize, 665usize, 0usize, 0usize]),
            (2usize, [666usize, 667usize, 0usize, 0usize]),
            (2usize, [668usize, 669usize, 0usize, 0usize]),
            (2usize, [670usize, 671usize, 0usize, 0usize]),
            (2usize, [672usize, 673usize, 0usize, 0usize]),
            (2usize, [674usize, 675usize, 0usize, 0usize]),
            (2usize, [676usize, 677usize, 0usize, 0usize]),
            (2usize, [678usize, 679usize, 0usize, 0usize]),
            (2usize, [680usize, 681usize, 0usize, 0usize]),
            (2usize, [682usize, 683usize, 0usize, 0usize]),
            (2usize, [684usize, 685usize, 0usize, 0usize]),
            (2usize, [686usize, 687usize, 0usize, 0usize]),
            (2usize, [688usize, 689usize, 0usize, 0usize]),
            (2usize, [690usize, 691usize, 0usize, 0usize]),
            (2usize, [692usize, 693usize, 0usize, 0usize]),
            (2usize, [694usize, 695usize, 0usize, 0usize]),
            (2usize, [696usize, 697usize, 0usize, 0usize]),
            (2usize, [698usize, 699usize, 0usize, 0usize]),
            (2usize, [700usize, 701usize, 0usize, 0usize]),
            (2usize, [702usize, 703usize, 0usize, 0usize]),
            (2usize, [704usize, 705usize, 0usize, 0usize]),
            (2usize, [706usize, 707usize, 0usize, 0usize]),
            (2usize, [708usize, 709usize, 0usize, 0usize]),
            (2usize, [710usize, 711usize, 0usize, 0usize]),
            (2usize, [712usize, 713usize, 0usize, 0usize]),
            (2usize, [714usize, 715usize, 0usize, 0usize]),
            (2usize, [716usize, 717usize, 0usize, 0usize]),
            (6usize, [627usize, 493usize, 629usize, 0usize]),
            (5usize, [628usize, 718usize, 0usize, 0usize]),
            (5usize, [719usize, 720usize, 0usize, 0usize]),
            (5usize, [721usize, 722usize, 0usize, 0usize]),
            (5usize, [723usize, 724usize, 0usize, 0usize]),
            (5usize, [725usize, 726usize, 0usize, 0usize]),
            (5usize, [727usize, 728usize, 0usize, 0usize]),
            (5usize, [729usize, 730usize, 0usize, 0usize]),
            (5usize, [731usize, 732usize, 0usize, 0usize]),
            (5usize, [733usize, 734usize, 0usize, 0usize]),
            (5usize, [735usize, 736usize, 0usize, 0usize]),
            (5usize, [737usize, 738usize, 0usize, 0usize]),
            (5usize, [739usize, 740usize, 0usize, 0usize]),
            (5usize, [741usize, 742usize, 0usize, 0usize]),
            (5usize, [743usize, 744usize, 0usize, 0usize]),
            (5usize, [745usize, 746usize, 0usize, 0usize]),
            (5usize, [747usize, 748usize, 0usize, 0usize]),
            (5usize, [749usize, 750usize, 0usize, 0usize]),
            (5usize, [751usize, 752usize, 0usize, 0usize]),
            (5usize, [753usize, 754usize, 0usize, 0usize]),
            (5usize, [755usize, 756usize, 0usize, 0usize]),
            (5usize, [757usize, 758usize, 0usize, 0usize]),
            (5usize, [759usize, 760usize, 0usize, 0usize]),
            (5usize, [761usize, 762usize, 0usize, 0usize]),
            (5usize, [763usize, 764usize, 0usize, 0usize]),
            (5usize, [765usize, 766usize, 0usize, 0usize]),
            (5usize, [767usize, 768usize, 0usize, 0usize]),
            (5usize, [769usize, 770usize, 0usize, 0usize]),
            (5usize, [771usize, 772usize, 0usize, 0usize]),
            (5usize, [773usize, 774usize, 0usize, 0usize]),
            (5usize, [775usize, 776usize, 0usize, 0usize]),
            (5usize, [777usize, 778usize, 0usize, 0usize]),
            (5usize, [779usize, 780usize, 0usize, 0usize]),
            (5usize, [781usize, 782usize, 0usize, 0usize]),
            (5usize, [783usize, 784usize, 0usize, 0usize]),
            (5usize, [785usize, 786usize, 0usize, 0usize]),
            (5usize, [787usize, 788usize, 0usize, 0usize]),
            (5usize, [789usize, 790usize, 0usize, 0usize]),
            (5usize, [791usize, 792usize, 0usize, 0usize]),
            (5usize, [793usize, 794usize, 0usize, 0usize]),
            (5usize, [795usize, 796usize, 0usize, 0usize]),
            (5usize, [797usize, 798usize, 0usize, 0usize]),
            (5usize, [799usize, 800usize, 0usize, 0usize]),
            (5usize, [801usize, 802usize, 0usize, 0usize]),
            (1usize, [803usize, 0usize, 0usize, 0usize]),
            (6usize, [804usize, 494usize, 805usize, 0usize]),
            (5usize, [806usize, 807usize, 0usize, 0usize]),
            (5usize, [808usize, 809usize, 0usize, 0usize]),
            (5usize, [810usize, 811usize, 0usize, 0usize]),
            (5usize, [812usize, 813usize, 0usize, 0usize]),
            (5usize, [814usize, 815usize, 0usize, 0usize]),
            (5usize, [816usize, 817usize, 0usize, 0usize]),
            (5usize, [818usize, 819usize, 0usize, 0usize]),
            (5usize, [820usize, 821usize, 0usize, 0usize]),
            (5usize, [822usize, 823usize, 0usize, 0usize]),
            (5usize, [824usize, 825usize, 0usize, 0usize]),
            (5usize, [826usize, 827usize, 0usize, 0usize]),
            (5usize, [828usize, 829usize, 0usize, 0usize]),
            (5usize, [830usize, 831usize, 0usize, 0usize]),
            (5usize, [832usize, 833usize, 0usize, 0usize]),
            (5usize, [834usize, 835usize, 0usize, 0usize]),
            (5usize, [836usize, 837usize, 0usize, 0usize]),
            (5usize, [838usize, 839usize, 0usize, 0usize]),
            (5usize, [840usize, 841usize, 0usize, 0usize]),
            (5usize, [842usize, 843usize, 0usize, 0usize]),
            (5usize, [844usize, 845usize, 0usize, 0usize]),
            (5usize, [846usize, 847usize, 0usize, 0usize]),
            (5usize, [848usize, 849usize, 0usize, 0usize]),
            (5usize, [850usize, 851usize, 0usize, 0usize]),
            (5usize, [852usize, 853usize, 0usize, 0usize]),
            (5usize, [854usize, 855usize, 0usize, 0usize]),
            (5usize, [856usize, 857usize, 0usize, 0usize]),
            (5usize, [858usize, 859usize, 0usize, 0usize]),
            (5usize, [860usize, 861usize, 0usize, 0usize]),
            (5usize, [862usize, 863usize, 0usize, 0usize]),
            (5usize, [864usize, 865usize, 0usize, 0usize]),
            (5usize, [866usize, 867usize, 0usize, 0usize]),
            (5usize, [868usize, 869usize, 0usize, 0usize]),
            (5usize, [870usize, 871usize, 0usize, 0usize]),
            (5usize, [872usize, 873usize, 0usize, 0usize]),
            (5usize, [874usize, 875usize, 0usize, 0usize]),
            (5usize, [876usize, 877usize, 0usize, 0usize]),
            (5usize, [878usize, 879usize, 0usize, 0usize]),
            (5usize, [880usize, 881usize, 0usize, 0usize]),
            (5usize, [882usize, 883usize, 0usize, 0usize]),
            (5usize, [884usize, 885usize, 0usize, 0usize]),
            (5usize, [886usize, 887usize, 0usize, 0usize]),
            (5usize, [888usize, 889usize, 0usize, 0usize]),
            (5usize, [890usize, 891usize, 0usize, 0usize]),
            (5usize, [892usize, 893usize, 0usize, 0usize]),
            (5usize, [894usize, 895usize, 0usize, 0usize]),
            (5usize, [896usize, 897usize, 0usize, 0usize]),
            (5usize, [898usize, 899usize, 0usize, 0usize]),
            (5usize, [900usize, 901usize, 0usize, 0usize]),
            (5usize, [902usize, 903usize, 0usize, 0usize]),
            (5usize, [904usize, 905usize, 0usize, 0usize]),
            (5usize, [906usize, 907usize, 0usize, 0usize]),
            (5usize, [908usize, 909usize, 0usize, 0usize]),
            (5usize, [910usize, 911usize, 0usize, 0usize]),
            (5usize, [912usize, 913usize, 0usize, 0usize]),
            (5usize, [914usize, 915usize, 0usize, 0usize]),
            (5usize, [916usize, 917usize, 0usize, 0usize]),
            (5usize, [918usize, 919usize, 0usize, 0usize]),
            (5usize, [920usize, 921usize, 0usize, 0usize]),
            (5usize, [922usize, 923usize, 0usize, 0usize]),
            (5usize, [924usize, 925usize, 0usize, 0usize]),
            (5usize, [926usize, 927usize, 0usize, 0usize]),
            (5usize, [928usize, 929usize, 0usize, 0usize]),
            (5usize, [930usize, 931usize, 0usize, 0usize]),
            (5usize, [932usize, 933usize, 0usize, 0usize]),
            (5usize, [934usize, 935usize, 0usize, 0usize]),
            (5usize, [936usize, 937usize, 0usize, 0usize]),
            (5usize, [938usize, 939usize, 0usize, 0usize]),
            (5usize, [940usize, 941usize, 0usize, 0usize]),
            (5usize, [942usize, 943usize, 0usize, 0usize]),
            (5usize, [944usize, 945usize, 0usize, 0usize]),
            (5usize, [946usize, 947usize, 0usize, 0usize]),
            (5usize, [948usize, 949usize, 0usize, 0usize]),
            (5usize, [950usize, 951usize, 0usize, 0usize]),
            (5usize, [952usize, 953usize, 0usize, 0usize]),
            (5usize, [954usize, 955usize, 0usize, 0usize]),
            (5usize, [956usize, 957usize, 0usize, 0usize]),
            (5usize, [958usize, 959usize, 0usize, 0usize]),
            (5usize, [960usize, 961usize, 0usize, 0usize]),
            (5usize, [962usize, 963usize, 0usize, 0usize]),
            (5usize, [964usize, 965usize, 0usize, 0usize]),
            (5usize, [966usize, 967usize, 0usize, 0usize]),
            (5usize, [968usize, 969usize, 0usize, 0usize]),
            (5usize, [970usize, 971usize, 0usize, 0usize]),
            (5usize, [972usize, 973usize, 0usize, 0usize]),
            (5usize, [974usize, 975usize, 0usize, 0usize]),
            (5usize, [976usize, 977usize, 0usize, 0usize]),
            (5usize, [978usize, 979usize, 0usize, 0usize]),
            (5usize, [980usize, 981usize, 0usize, 0usize]),
            (5usize, [982usize, 983usize, 0usize, 0usize]),
            (5usize, [984usize, 985usize, 0usize, 0usize]),
            (5usize, [986usize, 987usize, 0usize, 0usize]),
            (5usize, [988usize, 989usize, 0usize, 0usize]),
            (5usize, [990usize, 991usize, 0usize, 0usize]),
            (5usize, [992usize, 993usize, 0usize, 0usize]),
            (5usize, [994usize, 995usize, 0usize, 0usize]),
            (5usize, [996usize, 997usize, 0usize, 0usize]),
            (5usize, [998usize, 999usize, 0usize, 0usize]),
            (5usize, [1000usize, 1001usize, 0usize, 0usize]),
            (5usize, [1002usize, 1003usize, 0usize, 0usize]),
            (5usize, [1004usize, 1005usize, 0usize, 0usize]),
            (5usize, [1006usize, 1007usize, 0usize, 0usize]),
            (5usize, [1008usize, 1009usize, 0usize, 0usize]),
            (5usize, [1010usize, 1011usize, 0usize, 0usize]),
        ];
        let mut _sg = 0;
        while _sg < 194usize {
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
            let mut val = BabyBearExt4::ZERO;
            {
                field_ops::mul_assign(&mut val, &lookup_alpha);
                let mut col_val =
                    BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(1073741816u32));
                field_ops::add_assign(&mut val, &col_val);
            }
            {
                field_ops::mul_assign(&mut val, &lookup_alpha);
                let mut col_val =
                    BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                let mut ct = unsafe { evals.get_unchecked(449usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut ct,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut col_val, &ct);
                field_ops::add_assign(&mut val, &col_val);
            }
            {
                field_ops::mul_assign(&mut val, &lookup_alpha);
                let mut col_val =
                    BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                let mut ct = unsafe { evals.get_unchecked(445usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut ct,
                    &BabyBearField::from_reduced_raw_repr(536870908u32),
                );
                field_ops::add_assign(&mut col_val, &ct);
                let mut ct = unsafe { evals.get_unchecked(447usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut ct,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut col_val, &ct);
                field_ops::add_assign(&mut val, &col_val);
            }
            {
                field_ops::mul_assign(&mut val, &lookup_alpha);
                let mut col_val =
                    BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(0u32));
                let mut ct = unsafe { evals.get_unchecked(271usize) }[j];
                field_ops::mul_assign_by_base(
                    &mut ct,
                    &BabyBearField::from_reduced_raw_repr(268435454u32),
                );
                field_ops::add_assign(&mut col_val, &ct);
                field_ops::add_assign(&mut val, &col_val);
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
            let val = {
                let mut result: BabyBearExt4 = BabyBearExt4::ZERO;
                {
                    const CK_LIN_GROUPS: [(usize, usize, usize); 352usize] = [
                        (0usize, 0usize, 1usize),
                        (1usize, 1usize, 14usize),
                        (2usize, 15usize, 2usize),
                        (3usize, 17usize, 2usize),
                        (4usize, 19usize, 3usize),
                        (5usize, 22usize, 2usize),
                        (6usize, 24usize, 3usize),
                        (7usize, 27usize, 2usize),
                        (8usize, 29usize, 3usize),
                        (9usize, 32usize, 2usize),
                        (10usize, 34usize, 3usize),
                        (11usize, 37usize, 2usize),
                        (12usize, 39usize, 3usize),
                        (13usize, 42usize, 2usize),
                        (14usize, 44usize, 3usize),
                        (15usize, 47usize, 2usize),
                        (16usize, 49usize, 3usize),
                        (17usize, 52usize, 2usize),
                        (18usize, 54usize, 3usize),
                        (19usize, 57usize, 2usize),
                        (20usize, 59usize, 3usize),
                        (21usize, 62usize, 2usize),
                        (22usize, 64usize, 3usize),
                        (23usize, 67usize, 2usize),
                        (24usize, 69usize, 3usize),
                        (25usize, 72usize, 2usize),
                        (26usize, 74usize, 3usize),
                        (27usize, 77usize, 2usize),
                        (28usize, 79usize, 3usize),
                        (29usize, 82usize, 2usize),
                        (30usize, 84usize, 3usize),
                        (31usize, 87usize, 2usize),
                        (32usize, 89usize, 3usize),
                        (33usize, 92usize, 2usize),
                        (34usize, 94usize, 3usize),
                        (35usize, 97usize, 2usize),
                        (36usize, 99usize, 3usize),
                        (37usize, 102usize, 3usize),
                        (38usize, 105usize, 3usize),
                        (39usize, 108usize, 3usize),
                        (40usize, 111usize, 3usize),
                        (41usize, 114usize, 3usize),
                        (42usize, 117usize, 3usize),
                        (43usize, 120usize, 3usize),
                        (44usize, 123usize, 3usize),
                        (45usize, 126usize, 3usize),
                        (46usize, 129usize, 3usize),
                        (47usize, 132usize, 3usize),
                        (48usize, 135usize, 2usize),
                        (49usize, 137usize, 2usize),
                        (50usize, 139usize, 2usize),
                        (51usize, 141usize, 2usize),
                        (52usize, 143usize, 1usize),
                        (53usize, 144usize, 2usize),
                        (54usize, 146usize, 2usize),
                        (55usize, 148usize, 2usize),
                        (56usize, 150usize, 2usize),
                        (57usize, 152usize, 2usize),
                        (58usize, 154usize, 2usize),
                        (59usize, 156usize, 2usize),
                        (60usize, 158usize, 2usize),
                        (61usize, 160usize, 2usize),
                        (62usize, 162usize, 2usize),
                        (63usize, 164usize, 2usize),
                        (64usize, 166usize, 2usize),
                        (65usize, 168usize, 2usize),
                        (66usize, 170usize, 2usize),
                        (67usize, 172usize, 2usize),
                        (68usize, 174usize, 2usize),
                        (69usize, 176usize, 2usize),
                        (70usize, 178usize, 2usize),
                        (71usize, 180usize, 2usize),
                        (72usize, 182usize, 2usize),
                        (73usize, 184usize, 2usize),
                        (74usize, 186usize, 2usize),
                        (75usize, 188usize, 2usize),
                        (76usize, 190usize, 2usize),
                        (77usize, 192usize, 2usize),
                        (78usize, 194usize, 2usize),
                        (79usize, 196usize, 2usize),
                        (80usize, 198usize, 2usize),
                        (81usize, 200usize, 2usize),
                        (82usize, 202usize, 2usize),
                        (83usize, 204usize, 2usize),
                        (84usize, 206usize, 2usize),
                        (85usize, 208usize, 2usize),
                        (86usize, 210usize, 1usize),
                        (87usize, 211usize, 1usize),
                        (88usize, 212usize, 1usize),
                        (89usize, 213usize, 1usize),
                        (90usize, 214usize, 1usize),
                        (91usize, 215usize, 1usize),
                        (92usize, 216usize, 1usize),
                        (93usize, 217usize, 1usize),
                        (94usize, 218usize, 1usize),
                        (95usize, 219usize, 1usize),
                        (96usize, 220usize, 1usize),
                        (97usize, 221usize, 1usize),
                        (98usize, 222usize, 1usize),
                        (99usize, 223usize, 1usize),
                        (100usize, 224usize, 1usize),
                        (101usize, 225usize, 1usize),
                        (102usize, 226usize, 1usize),
                        (103usize, 227usize, 1usize),
                        (104usize, 228usize, 1usize),
                        (105usize, 229usize, 1usize),
                        (106usize, 230usize, 1usize),
                        (107usize, 231usize, 1usize),
                        (108usize, 232usize, 1usize),
                        (109usize, 233usize, 1usize),
                        (110usize, 234usize, 1usize),
                        (111usize, 235usize, 1usize),
                        (112usize, 236usize, 1usize),
                        (113usize, 237usize, 1usize),
                        (114usize, 238usize, 1usize),
                        (115usize, 239usize, 1usize),
                        (116usize, 240usize, 1usize),
                        (117usize, 241usize, 1usize),
                        (118usize, 242usize, 1usize),
                        (119usize, 243usize, 13usize),
                        (120usize, 256usize, 23usize),
                        (121usize, 279usize, 31usize),
                        (122usize, 310usize, 23usize),
                        (123usize, 333usize, 31usize),
                        (124usize, 364usize, 23usize),
                        (125usize, 387usize, 31usize),
                        (126usize, 418usize, 23usize),
                        (127usize, 441usize, 31usize),
                        (128usize, 472usize, 3usize),
                        (129usize, 475usize, 3usize),
                        (130usize, 478usize, 3usize),
                        (131usize, 481usize, 3usize),
                        (132usize, 484usize, 3usize),
                        (133usize, 487usize, 3usize),
                        (134usize, 490usize, 3usize),
                        (135usize, 493usize, 3usize),
                        (136usize, 496usize, 14usize),
                        (137usize, 510usize, 18usize),
                        (138usize, 528usize, 14usize),
                        (139usize, 542usize, 18usize),
                        (140usize, 560usize, 14usize),
                        (141usize, 574usize, 18usize),
                        (142usize, 592usize, 14usize),
                        (143usize, 606usize, 18usize),
                        (144usize, 624usize, 3usize),
                        (145usize, 627usize, 3usize),
                        (146usize, 630usize, 3usize),
                        (147usize, 633usize, 3usize),
                        (148usize, 636usize, 3usize),
                        (149usize, 639usize, 3usize),
                        (150usize, 642usize, 3usize),
                        (151usize, 645usize, 3usize),
                        (152usize, 648usize, 3usize),
                        (153usize, 651usize, 2usize),
                        (154usize, 653usize, 3usize),
                        (155usize, 656usize, 2usize),
                        (156usize, 658usize, 3usize),
                        (157usize, 661usize, 2usize),
                        (158usize, 663usize, 3usize),
                        (159usize, 666usize, 2usize),
                        (160usize, 668usize, 3usize),
                        (161usize, 671usize, 2usize),
                        (162usize, 673usize, 3usize),
                        (163usize, 676usize, 2usize),
                        (164usize, 678usize, 3usize),
                        (165usize, 681usize, 2usize),
                        (166usize, 683usize, 3usize),
                        (167usize, 686usize, 2usize),
                        (168usize, 688usize, 3usize),
                        (169usize, 691usize, 2usize),
                        (170usize, 693usize, 3usize),
                        (171usize, 696usize, 2usize),
                        (172usize, 698usize, 3usize),
                        (173usize, 701usize, 2usize),
                        (174usize, 703usize, 3usize),
                        (175usize, 706usize, 2usize),
                        (176usize, 708usize, 3usize),
                        (177usize, 711usize, 2usize),
                        (178usize, 713usize, 3usize),
                        (179usize, 716usize, 2usize),
                        (180usize, 718usize, 3usize),
                        (181usize, 721usize, 2usize),
                        (182usize, 723usize, 3usize),
                        (183usize, 726usize, 2usize),
                        (184usize, 728usize, 1usize),
                        (185usize, 729usize, 1usize),
                        (186usize, 730usize, 1usize),
                        (187usize, 731usize, 1usize),
                        (188usize, 732usize, 1usize),
                        (189usize, 733usize, 1usize),
                        (190usize, 734usize, 1usize),
                        (191usize, 735usize, 1usize),
                        (192usize, 736usize, 1usize),
                        (193usize, 737usize, 1usize),
                        (194usize, 738usize, 1usize),
                        (195usize, 739usize, 1usize),
                        (196usize, 740usize, 1usize),
                        (197usize, 741usize, 1usize),
                        (198usize, 742usize, 1usize),
                        (199usize, 743usize, 1usize),
                        (200usize, 744usize, 1usize),
                        (201usize, 745usize, 1usize),
                        (202usize, 746usize, 1usize),
                        (203usize, 747usize, 1usize),
                        (204usize, 748usize, 1usize),
                        (205usize, 749usize, 1usize),
                        (206usize, 750usize, 1usize),
                        (207usize, 751usize, 1usize),
                        (208usize, 752usize, 1usize),
                        (209usize, 753usize, 1usize),
                        (210usize, 754usize, 1usize),
                        (211usize, 755usize, 1usize),
                        (212usize, 756usize, 1usize),
                        (213usize, 757usize, 1usize),
                        (214usize, 758usize, 1usize),
                        (215usize, 759usize, 1usize),
                        (216usize, 760usize, 1usize),
                        (217usize, 761usize, 1usize),
                        (218usize, 762usize, 1usize),
                        (219usize, 763usize, 1usize),
                        (220usize, 764usize, 1usize),
                        (221usize, 765usize, 1usize),
                        (222usize, 766usize, 1usize),
                        (223usize, 767usize, 1usize),
                        (224usize, 768usize, 1usize),
                        (225usize, 769usize, 1usize),
                        (226usize, 770usize, 1usize),
                        (227usize, 771usize, 1usize),
                        (228usize, 772usize, 1usize),
                        (229usize, 773usize, 1usize),
                        (230usize, 774usize, 1usize),
                        (231usize, 775usize, 1usize),
                        (232usize, 776usize, 1usize),
                        (233usize, 777usize, 1usize),
                        (234usize, 778usize, 1usize),
                        (235usize, 779usize, 1usize),
                        (236usize, 780usize, 1usize),
                        (237usize, 781usize, 1usize),
                        (238usize, 782usize, 1usize),
                        (239usize, 783usize, 1usize),
                        (240usize, 784usize, 1usize),
                        (241usize, 785usize, 1usize),
                        (242usize, 786usize, 1usize),
                        (243usize, 787usize, 1usize),
                        (244usize, 788usize, 1usize),
                        (245usize, 789usize, 1usize),
                        (246usize, 790usize, 1usize),
                        (247usize, 791usize, 1usize),
                        (248usize, 792usize, 1usize),
                        (249usize, 793usize, 1usize),
                        (250usize, 794usize, 1usize),
                        (251usize, 795usize, 1usize),
                        (252usize, 796usize, 1usize),
                        (253usize, 797usize, 1usize),
                        (254usize, 798usize, 1usize),
                        (255usize, 799usize, 1usize),
                        (256usize, 800usize, 1usize),
                        (257usize, 801usize, 1usize),
                        (258usize, 802usize, 1usize),
                        (259usize, 803usize, 1usize),
                        (260usize, 804usize, 1usize),
                        (261usize, 805usize, 1usize),
                        (262usize, 806usize, 1usize),
                        (263usize, 807usize, 1usize),
                        (264usize, 808usize, 1usize),
                        (265usize, 809usize, 1usize),
                        (266usize, 810usize, 1usize),
                        (267usize, 811usize, 1usize),
                        (268usize, 812usize, 1usize),
                        (269usize, 813usize, 1usize),
                        (270usize, 814usize, 1usize),
                        (271usize, 815usize, 1usize),
                        (272usize, 816usize, 1usize),
                        (273usize, 817usize, 1usize),
                        (274usize, 818usize, 1usize),
                        (275usize, 819usize, 1usize),
                        (276usize, 820usize, 1usize),
                        (277usize, 821usize, 1usize),
                        (278usize, 822usize, 1usize),
                        (279usize, 823usize, 1usize),
                        (280usize, 824usize, 1usize),
                        (281usize, 825usize, 1usize),
                        (282usize, 826usize, 1usize),
                        (283usize, 827usize, 1usize),
                        (284usize, 828usize, 1usize),
                        (285usize, 829usize, 1usize),
                        (286usize, 830usize, 1usize),
                        (287usize, 831usize, 1usize),
                        (288usize, 832usize, 1usize),
                        (289usize, 833usize, 1usize),
                        (290usize, 834usize, 1usize),
                        (291usize, 835usize, 1usize),
                        (292usize, 836usize, 1usize),
                        (293usize, 837usize, 1usize),
                        (294usize, 838usize, 1usize),
                        (295usize, 839usize, 1usize),
                        (296usize, 840usize, 1usize),
                        (297usize, 841usize, 1usize),
                        (298usize, 842usize, 1usize),
                        (299usize, 843usize, 1usize),
                        (300usize, 844usize, 1usize),
                        (301usize, 845usize, 1usize),
                        (302usize, 846usize, 1usize),
                        (303usize, 847usize, 1usize),
                        (304usize, 848usize, 1usize),
                        (305usize, 849usize, 1usize),
                        (306usize, 850usize, 1usize),
                        (307usize, 851usize, 1usize),
                        (308usize, 852usize, 1usize),
                        (309usize, 853usize, 1usize),
                        (310usize, 854usize, 1usize),
                        (311usize, 855usize, 1usize),
                        (312usize, 856usize, 1usize),
                        (313usize, 857usize, 1usize),
                        (314usize, 858usize, 1usize),
                        (315usize, 859usize, 1usize),
                        (316usize, 860usize, 1usize),
                        (317usize, 861usize, 1usize),
                        (318usize, 862usize, 1usize),
                        (319usize, 863usize, 1usize),
                        (320usize, 864usize, 1usize),
                        (321usize, 865usize, 1usize),
                        (322usize, 866usize, 1usize),
                        (323usize, 867usize, 1usize),
                        (324usize, 868usize, 1usize),
                        (325usize, 869usize, 1usize),
                        (326usize, 870usize, 1usize),
                        (327usize, 871usize, 1usize),
                        (328usize, 872usize, 1usize),
                        (329usize, 873usize, 1usize),
                        (330usize, 874usize, 1usize),
                        (331usize, 875usize, 1usize),
                        (332usize, 876usize, 1usize),
                        (333usize, 877usize, 1usize),
                        (334usize, 878usize, 1usize),
                        (335usize, 879usize, 1usize),
                        (336usize, 880usize, 1usize),
                        (337usize, 881usize, 1usize),
                        (338usize, 882usize, 1usize),
                        (339usize, 883usize, 1usize),
                        (340usize, 884usize, 1usize),
                        (341usize, 885usize, 1usize),
                        (342usize, 886usize, 1usize),
                        (343usize, 887usize, 1usize),
                        (344usize, 888usize, 1usize),
                        (345usize, 889usize, 1usize),
                        (346usize, 890usize, 1usize),
                        (347usize, 891usize, 1usize),
                        (348usize, 892usize, 1usize),
                        (349usize, 893usize, 1usize),
                        (350usize, 894usize, 1usize),
                        (351usize, 895usize, 1usize),
                    ];
                    const CK_LIN_TERMS: [(u32, usize); 896usize] = [
                        (1744830467u32, 626usize),
                        (268435454u32, 0usize),
                        (536870908u32, 1usize),
                        (1073741816u32, 2usize),
                        (134217711u32, 3usize),
                        (268435422u32, 4usize),
                        (536870844u32, 5usize),
                        (1073741688u32, 6usize),
                        (134217455u32, 7usize),
                        (268434910u32, 8usize),
                        (536869820u32, 9usize),
                        (1073739640u32, 10usize),
                        (134213359u32, 11usize),
                        (268426718u32, 12usize),
                        (1744830467u32, 623usize),
                        (268435454u32, 12usize),
                        (1744830467u32, 13usize),
                        (268435454u32, 3usize),
                        (1744830467u32, 14usize),
                        (268309694u32, 2usize),
                        (1744830467u32, 15usize),
                        (268435454u32, 495usize),
                        (1744830467u32, 16usize),
                        (268435454u32, 527usize),
                        (671030187u32, 2usize),
                        (1744830467u32, 17usize),
                        (268435454u32, 496usize),
                        (1744830467u32, 18usize),
                        (268435454u32, 528usize),
                        (1878952882u32, 2usize),
                        (1744830467u32, 19usize),
                        (268435454u32, 499usize),
                        (1744830467u32, 20usize),
                        (268435454u32, 531usize),
                        (1342074934u32, 2usize),
                        (1744830467u32, 21usize),
                        (268435454u32, 500usize),
                        (1744830467u32, 22usize),
                        (268435454u32, 532usize),
                        (1207826599u32, 2usize),
                        (1744830467u32, 23usize),
                        (268435454u32, 503usize),
                        (1744830467u32, 24usize),
                        (268435454u32, 535usize),
                        (1342144278u32, 2usize),
                        (1744830467u32, 25usize),
                        (268435454u32, 504usize),
                        (1744830467u32, 26usize),
                        (268435454u32, 536usize),
                        (805172442u32, 2usize),
                        (1744830467u32, 27usize),
                        (268435454u32, 507usize),
                        (1744830467u32, 28usize),
                        (268435454u32, 539usize),
                        (1073651544u32, 2usize),
                        (1744830467u32, 29usize),
                        (268435454u32, 508usize),
                        (1744830467u32, 30usize),
                        (268435454u32, 540usize),
                        (1744785411u32, 2usize),
                        (1744830467u32, 31usize),
                        (268435454u32, 511usize),
                        (1744830467u32, 32usize),
                        (268435454u32, 543usize),
                        (1342133014u32, 2usize),
                        (1744830467u32, 33usize),
                        (268435454u32, 512usize),
                        (1744830467u32, 34usize),
                        (268435454u32, 544usize),
                        (1073684728u32, 2usize),
                        (1744830467u32, 35usize),
                        (268435454u32, 515usize),
                        (1744830467u32, 36usize),
                        (268435454u32, 547usize),
                        (671003979u32, 2usize),
                        (1744830467u32, 37usize),
                        (268435454u32, 516usize),
                        (1744830467u32, 38usize),
                        (268435454u32, 548usize),
                        (1476276133u32, 2usize),
                        (1744830467u32, 39usize),
                        (268435454u32, 519usize),
                        (1744830467u32, 40usize),
                        (268435454u32, 551usize),
                        (1207942343u32, 2usize),
                        (1744830467u32, 41usize),
                        (268435454u32, 520usize),
                        (1744830467u32, 42usize),
                        (268435454u32, 552usize),
                        (1342065270u32, 2usize),
                        (1744830467u32, 43usize),
                        (268435454u32, 523usize),
                        (1744830467u32, 44usize),
                        (268435454u32, 555usize),
                        (2013215745u32, 2usize),
                        (1744830467u32, 45usize),
                        (268435454u32, 524usize),
                        (1744830467u32, 46usize),
                        (268435454u32, 556usize),
                        (805180538u32, 3usize),
                        (1744830467u32, 47usize),
                        (268435454u32, 559usize),
                        (671030731u32, 3usize),
                        (1744830467u32, 48usize),
                        (268435454u32, 560usize),
                        (1878952882u32, 3usize),
                        (1744830467u32, 49usize),
                        (268435454u32, 563usize),
                        (1342074934u32, 3usize),
                        (1744830467u32, 50usize),
                        (268435454u32, 564usize),
                        (1207826599u32, 3usize),
                        (1744830467u32, 51usize),
                        (268435454u32, 567usize),
                        (1342144278u32, 3usize),
                        (1744830467u32, 52usize),
                        (268435454u32, 568usize),
                        (805172442u32, 3usize),
                        (1744830467u32, 53usize),
                        (268435454u32, 571usize),
                        (1073651544u32, 3usize),
                        (1744830467u32, 54usize),
                        (268435454u32, 572usize),
                        (1073684728u32, 3usize),
                        (1744830467u32, 55usize),
                        (268435454u32, 579usize),
                        (671003979u32, 3usize),
                        (1744830467u32, 56usize),
                        (268435454u32, 580usize),
                        (1342065270u32, 3usize),
                        (1744830467u32, 57usize),
                        (268435454u32, 587usize),
                        (2013215745u32, 3usize),
                        (1744830467u32, 58usize),
                        (268435454u32, 588usize),
                        (1744830467u32, 59usize),
                        (268435454u32, 575usize),
                        (1744830467u32, 60usize),
                        (268435454u32, 576usize),
                        (1744830467u32, 61usize),
                        (268435454u32, 583usize),
                        (1744830467u32, 62usize),
                        (268435454u32, 584usize),
                        (1744830467u32, 63usize),
                        (268435454u32, 2usize),
                        (1744830467u32, 64usize),
                        (1744830467u32, 65usize),
                        (268435454u32, 591usize),
                        (1744830467u32, 66usize),
                        (268435454u32, 592usize),
                        (1744830467u32, 67usize),
                        (268435454u32, 593usize),
                        (1744830467u32, 68usize),
                        (268435454u32, 594usize),
                        (1744830467u32, 69usize),
                        (268435454u32, 595usize),
                        (1744830467u32, 70usize),
                        (268435454u32, 596usize),
                        (1744830467u32, 71usize),
                        (268435454u32, 597usize),
                        (1744830467u32, 72usize),
                        (268435454u32, 598usize),
                        (1744830467u32, 73usize),
                        (268435454u32, 599usize),
                        (1744830467u32, 74usize),
                        (268435454u32, 600usize),
                        (1744830467u32, 75usize),
                        (268435454u32, 601usize),
                        (1744830467u32, 76usize),
                        (268435454u32, 602usize),
                        (1744830467u32, 77usize),
                        (268435454u32, 603usize),
                        (1744830467u32, 78usize),
                        (268435454u32, 604usize),
                        (1744830467u32, 79usize),
                        (268435454u32, 605usize),
                        (1744830467u32, 80usize),
                        (268435454u32, 606usize),
                        (1744830467u32, 81usize),
                        (268435454u32, 607usize),
                        (1744830467u32, 82usize),
                        (268435454u32, 608usize),
                        (1744830467u32, 83usize),
                        (268435454u32, 609usize),
                        (1744830467u32, 84usize),
                        (268435454u32, 610usize),
                        (1744830467u32, 85usize),
                        (268435454u32, 611usize),
                        (1744830467u32, 86usize),
                        (268435454u32, 612usize),
                        (1744830467u32, 87usize),
                        (268435454u32, 613usize),
                        (1744830467u32, 88usize),
                        (268435454u32, 614usize),
                        (1744830467u32, 89usize),
                        (268435454u32, 615usize),
                        (1744830467u32, 90usize),
                        (268435454u32, 616usize),
                        (1744830467u32, 91usize),
                        (268435454u32, 617usize),
                        (1744830467u32, 92usize),
                        (268435454u32, 618usize),
                        (1744830467u32, 93usize),
                        (268435454u32, 619usize),
                        (1744830467u32, 94usize),
                        (268435454u32, 620usize),
                        (1744830467u32, 95usize),
                        (268435454u32, 621usize),
                        (1744830467u32, 96usize),
                        (268435454u32, 622usize),
                        (1744830467u32, 97usize),
                        (1744830467u32, 98usize),
                        (1744830467u32, 99usize),
                        (1744830467u32, 100usize),
                        (1744830467u32, 101usize),
                        (1744830467u32, 102usize),
                        (1744830467u32, 103usize),
                        (1744830467u32, 104usize),
                        (1744830467u32, 105usize),
                        (1744830467u32, 106usize),
                        (1744830467u32, 107usize),
                        (1744830467u32, 108usize),
                        (1744830467u32, 109usize),
                        (1744830467u32, 110usize),
                        (1744830467u32, 111usize),
                        (1744830467u32, 112usize),
                        (1744830467u32, 113usize),
                        (1744830467u32, 114usize),
                        (1744830467u32, 115usize),
                        (1744830467u32, 116usize),
                        (1744830467u32, 117usize),
                        (1744830467u32, 118usize),
                        (1744830467u32, 119usize),
                        (1744830467u32, 120usize),
                        (1744830467u32, 121usize),
                        (1744830467u32, 122usize),
                        (1744830467u32, 123usize),
                        (1744830467u32, 124usize),
                        (1744830467u32, 125usize),
                        (1744830467u32, 126usize),
                        (1744830467u32, 127usize),
                        (1744830467u32, 128usize),
                        (268435454u32, 624usize),
                        (268435454u32, 0usize),
                        (536870908u32, 1usize),
                        (1073741816u32, 2usize),
                        (268435422u32, 3usize),
                        (536870844u32, 4usize),
                        (1073741688u32, 5usize),
                        (134217455u32, 6usize),
                        (268434910u32, 7usize),
                        (536869820u32, 8usize),
                        (1073739640u32, 9usize),
                        (134213359u32, 10usize),
                        (268426718u32, 11usize),
                        (1744830467u32, 625usize),
                        (268435454u32, 16usize),
                        (268435454u32, 32usize),
                        (268435454u32, 97usize),
                        (268435454u32, 99usize),
                        (268435454u32, 113usize),
                        (268435454u32, 115usize),
                        (1744970275u32, 129usize),
                        (1476674629u32, 130usize),
                        (268435454u32, 141usize),
                        (268435422u32, 142usize),
                        (134217455u32, 143usize),
                        (1744970275u32, 145usize),
                        (1476674629u32, 146usize),
                        (268435454u32, 186usize),
                        (536869820u32, 187usize),
                        (1744970275u32, 249usize),
                        (1476674629u32, 250usize),
                        (268435454u32, 261usize),
                        (268435422u32, 262usize),
                        (134217455u32, 263usize),
                        (1744970275u32, 265usize),
                        (1476674629u32, 266usize),
                        (1744830467u32, 529usize),
                        (268435454u32, 18usize),
                        (268435454u32, 34usize),
                        (268435454u32, 98usize),
                        (268435454u32, 100usize),
                        (268435454u32, 114usize),
                        (268435454u32, 116usize),
                        (268435454u32, 129usize),
                        (536870908u32, 130usize),
                        (1744970275u32, 131usize),
                        (1476674629u32, 132usize),
                        (268435422u32, 139usize),
                        (134217455u32, 140usize),
                        (268435454u32, 144usize),
                        (268435454u32, 145usize),
                        (536870908u32, 146usize),
                        (1744970275u32, 147usize),
                        (1476674629u32, 148usize),
                        (536869820u32, 185usize),
                        (268435454u32, 188usize),
                        (268435454u32, 249usize),
                        (536870908u32, 250usize),
                        (1744970275u32, 251usize),
                        (1476674629u32, 252usize),
                        (268435422u32, 259usize),
                        (134217455u32, 260usize),
                        (268435454u32, 264usize),
                        (268435454u32, 265usize),
                        (536870908u32, 266usize),
                        (1744970275u32, 267usize),
                        (1476674629u32, 268usize),
                        (1744830467u32, 530usize),
                        (268435454u32, 20usize),
                        (268435454u32, 36usize),
                        (268435454u32, 101usize),
                        (268435454u32, 103usize),
                        (268435454u32, 117usize),
                        (268435454u32, 119usize),
                        (1744970275u32, 159usize),
                        (1476674629u32, 160usize),
                        (268435454u32, 171usize),
                        (268435422u32, 172usize),
                        (134217455u32, 173usize),
                        (1744970275u32, 175usize),
                        (1476674629u32, 176usize),
                        (268435454u32, 216usize),
                        (536869820u32, 217usize),
                        (1744970275u32, 281usize),
                        (1476674629u32, 282usize),
                        (268435454u32, 293usize),
                        (268435422u32, 294usize),
                        (134217455u32, 295usize),
                        (1744970275u32, 297usize),
                        (1476674629u32, 298usize),
                        (1744830467u32, 533usize),
                        (268435454u32, 22usize),
                        (268435454u32, 38usize),
                        (268435454u32, 102usize),
                        (268435454u32, 104usize),
                        (268435454u32, 118usize),
                        (268435454u32, 120usize),
                        (268435454u32, 159usize),
                        (536870908u32, 160usize),
                        (1744970275u32, 161usize),
                        (1476674629u32, 162usize),
                        (268435422u32, 169usize),
                        (134217455u32, 170usize),
                        (268435454u32, 174usize),
                        (268435454u32, 175usize),
                        (536870908u32, 176usize),
                        (1744970275u32, 177usize),
                        (1476674629u32, 178usize),
                        (536869820u32, 215usize),
                        (268435454u32, 218usize),
                        (268435454u32, 281usize),
                        (536870908u32, 282usize),
                        (1744970275u32, 283usize),
                        (1476674629u32, 284usize),
                        (268435422u32, 291usize),
                        (134217455u32, 292usize),
                        (268435454u32, 296usize),
                        (268435454u32, 297usize),
                        (536870908u32, 298usize),
                        (1744970275u32, 299usize),
                        (1476674629u32, 300usize),
                        (1744830467u32, 534usize),
                        (268435454u32, 24usize),
                        (268435454u32, 40usize),
                        (268435454u32, 105usize),
                        (268435454u32, 107usize),
                        (268435454u32, 121usize),
                        (268435454u32, 123usize),
                        (1744970275u32, 189usize),
                        (1476674629u32, 190usize),
                        (268435454u32, 201usize),
                        (268435422u32, 202usize),
                        (134217455u32, 203usize),
                        (1744970275u32, 205usize),
                        (1476674629u32, 206usize),
                        (268435454u32, 246usize),
                        (536869820u32, 247usize),
                        (1744970275u32, 313usize),
                        (1476674629u32, 314usize),
                        (268435454u32, 325usize),
                        (268435422u32, 326usize),
                        (134217455u32, 327usize),
                        (1744970275u32, 329usize),
                        (1476674629u32, 330usize),
                        (1744830467u32, 537usize),
                        (268435454u32, 26usize),
                        (268435454u32, 42usize),
                        (268435454u32, 106usize),
                        (268435454u32, 108usize),
                        (268435454u32, 122usize),
                        (268435454u32, 124usize),
                        (268435454u32, 189usize),
                        (536870908u32, 190usize),
                        (1744970275u32, 191usize),
                        (1476674629u32, 192usize),
                        (268435422u32, 199usize),
                        (134217455u32, 200usize),
                        (268435454u32, 204usize),
                        (268435454u32, 205usize),
                        (536870908u32, 206usize),
                        (1744970275u32, 207usize),
                        (1476674629u32, 208usize),
                        (536869820u32, 245usize),
                        (268435454u32, 248usize),
                        (268435454u32, 313usize),
                        (536870908u32, 314usize),
                        (1744970275u32, 315usize),
                        (1476674629u32, 316usize),
                        (268435422u32, 323usize),
                        (134217455u32, 324usize),
                        (268435454u32, 328usize),
                        (268435454u32, 329usize),
                        (536870908u32, 330usize),
                        (1744970275u32, 331usize),
                        (1476674629u32, 332usize),
                        (1744830467u32, 538usize),
                        (268435454u32, 28usize),
                        (268435454u32, 44usize),
                        (268435454u32, 109usize),
                        (268435454u32, 111usize),
                        (268435454u32, 125usize),
                        (268435454u32, 127usize),
                        (268435454u32, 156usize),
                        (536869820u32, 157usize),
                        (1744970275u32, 219usize),
                        (1476674629u32, 220usize),
                        (268435454u32, 231usize),
                        (268435422u32, 232usize),
                        (134217455u32, 233usize),
                        (1744970275u32, 235usize),
                        (1476674629u32, 236usize),
                        (1744970275u32, 345usize),
                        (1476674629u32, 346usize),
                        (268435454u32, 357usize),
                        (268435422u32, 358usize),
                        (134217455u32, 359usize),
                        (1744970275u32, 361usize),
                        (1476674629u32, 362usize),
                        (1744830467u32, 541usize),
                        (268435454u32, 30usize),
                        (268435454u32, 46usize),
                        (268435454u32, 110usize),
                        (268435454u32, 112usize),
                        (268435454u32, 126usize),
                        (268435454u32, 128usize),
                        (536869820u32, 155usize),
                        (268435454u32, 158usize),
                        (268435454u32, 219usize),
                        (536870908u32, 220usize),
                        (1744970275u32, 221usize),
                        (1476674629u32, 222usize),
                        (268435422u32, 229usize),
                        (134217455u32, 230usize),
                        (268435454u32, 234usize),
                        (268435454u32, 235usize),
                        (536870908u32, 236usize),
                        (1744970275u32, 237usize),
                        (1476674629u32, 238usize),
                        (268435454u32, 345usize),
                        (536870908u32, 346usize),
                        (1744970275u32, 347usize),
                        (1476674629u32, 348usize),
                        (268435422u32, 355usize),
                        (134217455u32, 356usize),
                        (268435454u32, 360usize),
                        (268435454u32, 361usize),
                        (536870908u32, 362usize),
                        (1744970275u32, 363usize),
                        (1476674629u32, 364usize),
                        (1744830467u32, 542usize),
                        (268435454u32, 374usize),
                        (536869820u32, 375usize),
                        (1744830467u32, 545usize),
                        (536869820u32, 373usize),
                        (268435454u32, 376usize),
                        (1744830467u32, 546usize),
                        (268435454u32, 278usize),
                        (536869820u32, 279usize),
                        (1744830467u32, 549usize),
                        (536869820u32, 277usize),
                        (268435454u32, 280usize),
                        (1744830467u32, 550usize),
                        (268435454u32, 310usize),
                        (536869820u32, 311usize),
                        (1744830467u32, 553usize),
                        (536869820u32, 309usize),
                        (268435454u32, 312usize),
                        (1744830467u32, 554usize),
                        (268435454u32, 342usize),
                        (536869820u32, 343usize),
                        (1744830467u32, 557usize),
                        (536869820u32, 341usize),
                        (268435454u32, 344usize),
                        (1744830467u32, 558usize),
                        (268435454u32, 47usize),
                        (268435454u32, 135usize),
                        (268434910u32, 136usize),
                        (1744970275u32, 137usize),
                        (268435454u32, 150usize),
                        (268434910u32, 151usize),
                        (1744970275u32, 153usize),
                        (268435454u32, 319usize),
                        (268434910u32, 320usize),
                        (1744970275u32, 321usize),
                        (268435454u32, 336usize),
                        (268434910u32, 337usize),
                        (1744970275u32, 339usize),
                        (1744830467u32, 561usize),
                        (268435454u32, 48usize),
                        (268435454u32, 133usize),
                        (268434910u32, 134usize),
                        (268435454u32, 137usize),
                        (1744970275u32, 138usize),
                        (268434910u32, 149usize),
                        (268435454u32, 152usize),
                        (268435454u32, 153usize),
                        (1744970275u32, 154usize),
                        (268435454u32, 317usize),
                        (268434910u32, 318usize),
                        (268435454u32, 321usize),
                        (1744970275u32, 322usize),
                        (268434910u32, 335usize),
                        (268435454u32, 338usize),
                        (268435454u32, 339usize),
                        (1744970275u32, 340usize),
                        (1744830467u32, 562usize),
                        (268435454u32, 49usize),
                        (268435454u32, 165usize),
                        (268434910u32, 166usize),
                        (1744970275u32, 167usize),
                        (268435454u32, 180usize),
                        (268434910u32, 181usize),
                        (1744970275u32, 183usize),
                        (268435454u32, 351usize),
                        (268434910u32, 352usize),
                        (1744970275u32, 353usize),
                        (268435454u32, 368usize),
                        (268434910u32, 369usize),
                        (1744970275u32, 371usize),
                        (1744830467u32, 565usize),
                        (268435454u32, 50usize),
                        (268435454u32, 163usize),
                        (268434910u32, 164usize),
                        (268435454u32, 167usize),
                        (1744970275u32, 168usize),
                        (268434910u32, 179usize),
                        (268435454u32, 182usize),
                        (268435454u32, 183usize),
                        (1744970275u32, 184usize),
                        (268435454u32, 349usize),
                        (268434910u32, 350usize),
                        (268435454u32, 353usize),
                        (1744970275u32, 354usize),
                        (268434910u32, 367usize),
                        (268435454u32, 370usize),
                        (268435454u32, 371usize),
                        (1744970275u32, 372usize),
                        (1744830467u32, 566usize),
                        (268435454u32, 51usize),
                        (268435454u32, 195usize),
                        (268434910u32, 196usize),
                        (1744970275u32, 197usize),
                        (268435454u32, 210usize),
                        (268434910u32, 211usize),
                        (1744970275u32, 213usize),
                        (268435454u32, 255usize),
                        (268434910u32, 256usize),
                        (1744970275u32, 257usize),
                        (268435454u32, 272usize),
                        (268434910u32, 273usize),
                        (1744970275u32, 275usize),
                        (1744830467u32, 569usize),
                        (268435454u32, 52usize),
                        (268435454u32, 193usize),
                        (268434910u32, 194usize),
                        (268435454u32, 197usize),
                        (1744970275u32, 198usize),
                        (268434910u32, 209usize),
                        (268435454u32, 212usize),
                        (268435454u32, 213usize),
                        (1744970275u32, 214usize),
                        (268435454u32, 253usize),
                        (268434910u32, 254usize),
                        (268435454u32, 257usize),
                        (1744970275u32, 258usize),
                        (268434910u32, 271usize),
                        (268435454u32, 274usize),
                        (268435454u32, 275usize),
                        (1744970275u32, 276usize),
                        (1744830467u32, 570usize),
                        (268435454u32, 53usize),
                        (268435454u32, 225usize),
                        (268434910u32, 226usize),
                        (1744970275u32, 227usize),
                        (268435454u32, 240usize),
                        (268434910u32, 241usize),
                        (1744970275u32, 243usize),
                        (268435454u32, 287usize),
                        (268434910u32, 288usize),
                        (1744970275u32, 289usize),
                        (268435454u32, 304usize),
                        (268434910u32, 305usize),
                        (1744970275u32, 307usize),
                        (1744830467u32, 573usize),
                        (268435454u32, 54usize),
                        (268435454u32, 223usize),
                        (268434910u32, 224usize),
                        (268435454u32, 227usize),
                        (1744970275u32, 228usize),
                        (268434910u32, 239usize),
                        (268435454u32, 242usize),
                        (268435454u32, 243usize),
                        (1744970275u32, 244usize),
                        (268435454u32, 285usize),
                        (268434910u32, 286usize),
                        (268435454u32, 289usize),
                        (1744970275u32, 290usize),
                        (268434910u32, 303usize),
                        (268435454u32, 306usize),
                        (268435454u32, 307usize),
                        (1744970275u32, 308usize),
                        (1744830467u32, 574usize),
                        (268435454u32, 304usize),
                        (268434910u32, 305usize),
                        (1744830467u32, 577usize),
                        (268434910u32, 303usize),
                        (268435454u32, 306usize),
                        (1744830467u32, 578usize),
                        (268435454u32, 336usize),
                        (268434910u32, 337usize),
                        (1744830467u32, 581usize),
                        (268434910u32, 335usize),
                        (268435454u32, 338usize),
                        (1744830467u32, 582usize),
                        (268435454u32, 368usize),
                        (268434910u32, 369usize),
                        (1744830467u32, 585usize),
                        (268434910u32, 367usize),
                        (268435454u32, 370usize),
                        (1744830467u32, 586usize),
                        (268435454u32, 272usize),
                        (268434910u32, 273usize),
                        (1744830467u32, 589usize),
                        (268434910u32, 271usize),
                        (268435454u32, 274usize),
                        (1744830467u32, 590usize),
                        (268435454u32, 269usize),
                        (1744830467u32, 377usize),
                        (1879048466u32, 378usize),
                        (268435454u32, 495usize),
                        (1744830467u32, 497usize),
                        (268435454u32, 270usize),
                        (1744830467u32, 381usize),
                        (1879048466u32, 382usize),
                        (268435454u32, 496usize),
                        (1744830467u32, 498usize),
                        (268435454u32, 301usize),
                        (1744830467u32, 385usize),
                        (1879048466u32, 386usize),
                        (268435454u32, 499usize),
                        (1744830467u32, 501usize),
                        (268435454u32, 302usize),
                        (1744830467u32, 389usize),
                        (1879048466u32, 390usize),
                        (268435454u32, 500usize),
                        (1744830467u32, 502usize),
                        (268435454u32, 333usize),
                        (1744830467u32, 393usize),
                        (1879048466u32, 394usize),
                        (268435454u32, 503usize),
                        (1744830467u32, 505usize),
                        (268435454u32, 334usize),
                        (1744830467u32, 397usize),
                        (1879048466u32, 398usize),
                        (268435454u32, 504usize),
                        (1744830467u32, 506usize),
                        (268435454u32, 365usize),
                        (1744830467u32, 401usize),
                        (1879048466u32, 402usize),
                        (268435454u32, 507usize),
                        (1744830467u32, 509usize),
                        (268435454u32, 366usize),
                        (1744830467u32, 405usize),
                        (1879048466u32, 406usize),
                        (268435454u32, 508usize),
                        (1744830467u32, 510usize),
                        (268435454u32, 409usize),
                        (1744830467u32, 410usize),
                        (1744831011u32, 411usize),
                        (268435454u32, 511usize),
                        (1744830467u32, 513usize),
                        (268435454u32, 414usize),
                        (1744830467u32, 415usize),
                        (1744831011u32, 416usize),
                        (268435454u32, 512usize),
                        (1744830467u32, 514usize),
                        (268435454u32, 419usize),
                        (1744830467u32, 420usize),
                        (1744831011u32, 421usize),
                        (268435454u32, 515usize),
                        (1744830467u32, 517usize),
                        (268435454u32, 424usize),
                        (1744830467u32, 425usize),
                        (1744831011u32, 426usize),
                        (268435454u32, 516usize),
                        (1744830467u32, 518usize),
                        (268435454u32, 429usize),
                        (1744830467u32, 430usize),
                        (1744831011u32, 431usize),
                        (268435454u32, 519usize),
                        (1744830467u32, 521usize),
                        (268435454u32, 434usize),
                        (1744830467u32, 435usize),
                        (1744831011u32, 436usize),
                        (268435454u32, 520usize),
                        (1744830467u32, 522usize),
                        (268435454u32, 439usize),
                        (1744830467u32, 440usize),
                        (1744831011u32, 441usize),
                        (268435454u32, 523usize),
                        (1744830467u32, 525usize),
                        (268435454u32, 444usize),
                        (1744830467u32, 446usize),
                        (1744831011u32, 447usize),
                        (268435454u32, 524usize),
                        (1744830467u32, 526usize),
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
                        (1744830467u32, 129usize),
                        (1744830467u32, 130usize),
                        (1744830467u32, 131usize),
                        (1744830467u32, 132usize),
                        (1744830467u32, 137usize),
                        (1744830467u32, 138usize),
                        (1744830467u32, 145usize),
                        (1744830467u32, 146usize),
                        (1744830467u32, 147usize),
                        (1744830467u32, 148usize),
                        (1744830467u32, 153usize),
                        (1744830467u32, 154usize),
                        (1744830467u32, 159usize),
                        (1744830467u32, 160usize),
                        (1744830467u32, 161usize),
                        (1744830467u32, 162usize),
                        (1744830467u32, 167usize),
                        (1744830467u32, 168usize),
                        (1744830467u32, 175usize),
                        (1744830467u32, 176usize),
                        (1744830467u32, 177usize),
                        (1744830467u32, 178usize),
                        (1744830467u32, 183usize),
                        (1744830467u32, 184usize),
                        (1744830467u32, 189usize),
                        (1744830467u32, 190usize),
                        (1744830467u32, 191usize),
                        (1744830467u32, 192usize),
                        (1744830467u32, 197usize),
                        (1744830467u32, 198usize),
                        (1744830467u32, 205usize),
                        (1744830467u32, 206usize),
                        (1744830467u32, 207usize),
                        (1744830467u32, 208usize),
                        (1744830467u32, 213usize),
                        (1744830467u32, 214usize),
                        (1744830467u32, 219usize),
                        (1744830467u32, 220usize),
                        (1744830467u32, 221usize),
                        (1744830467u32, 222usize),
                        (1744830467u32, 227usize),
                        (1744830467u32, 228usize),
                        (1744830467u32, 235usize),
                        (1744830467u32, 236usize),
                        (1744830467u32, 237usize),
                        (1744830467u32, 238usize),
                        (1744830467u32, 243usize),
                        (1744830467u32, 244usize),
                        (1744830467u32, 249usize),
                        (1744830467u32, 250usize),
                        (1744830467u32, 251usize),
                        (1744830467u32, 252usize),
                        (1744830467u32, 257usize),
                        (1744830467u32, 258usize),
                        (1744830467u32, 265usize),
                        (1744830467u32, 266usize),
                        (1744830467u32, 267usize),
                        (1744830467u32, 268usize),
                        (1744830467u32, 275usize),
                        (1744830467u32, 276usize),
                        (1744830467u32, 281usize),
                        (1744830467u32, 282usize),
                        (1744830467u32, 283usize),
                        (1744830467u32, 284usize),
                        (1744830467u32, 289usize),
                        (1744830467u32, 290usize),
                        (1744830467u32, 297usize),
                        (1744830467u32, 298usize),
                        (1744830467u32, 299usize),
                        (1744830467u32, 300usize),
                        (1744830467u32, 307usize),
                        (1744830467u32, 308usize),
                        (1744830467u32, 313usize),
                        (1744830467u32, 314usize),
                        (1744830467u32, 315usize),
                        (1744830467u32, 316usize),
                        (1744830467u32, 321usize),
                        (1744830467u32, 322usize),
                        (1744830467u32, 329usize),
                        (1744830467u32, 330usize),
                        (1744830467u32, 331usize),
                        (1744830467u32, 332usize),
                        (1744830467u32, 339usize),
                        (1744830467u32, 340usize),
                        (1744830467u32, 345usize),
                        (1744830467u32, 346usize),
                        (1744830467u32, 347usize),
                        (1744830467u32, 348usize),
                        (1744830467u32, 353usize),
                        (1744830467u32, 354usize),
                        (1744830467u32, 361usize),
                        (1744830467u32, 362usize),
                        (1744830467u32, 363usize),
                        (1744830467u32, 364usize),
                        (1744830467u32, 371usize),
                        (1744830467u32, 372usize),
                        (1744830467u32, 378usize),
                        (1744830467u32, 382usize),
                        (1744830467u32, 386usize),
                        (1744830467u32, 390usize),
                        (1744830467u32, 394usize),
                        (1744830467u32, 398usize),
                        (1744830467u32, 402usize),
                        (1744830467u32, 406usize),
                        (1744830467u32, 411usize),
                        (1744830467u32, 416usize),
                        (1744830467u32, 421usize),
                        (1744830467u32, 426usize),
                        (1744830467u32, 431usize),
                        (1744830467u32, 436usize),
                        (1744830467u32, 441usize),
                        (1744830467u32, 447usize),
                        (1744830467u32, 450usize),
                        (1744830467u32, 451usize),
                        (1744830467u32, 452usize),
                        (1744830467u32, 453usize),
                        (1744830467u32, 454usize),
                        (1744830467u32, 455usize),
                        (1744830467u32, 456usize),
                        (1744830467u32, 457usize),
                        (1744830467u32, 458usize),
                        (1744830467u32, 459usize),
                        (1744830467u32, 460usize),
                        (1744830467u32, 461usize),
                        (1744830467u32, 462usize),
                        (1744830467u32, 463usize),
                        (1744830467u32, 464usize),
                        (1744830467u32, 465usize),
                        (1744830467u32, 466usize),
                        (1744830467u32, 467usize),
                        (1744830467u32, 468usize),
                        (1744830467u32, 469usize),
                        (1744830467u32, 470usize),
                        (1744830467u32, 471usize),
                        (1744830467u32, 472usize),
                        (1744830467u32, 473usize),
                        (1744830467u32, 474usize),
                        (1744830467u32, 475usize),
                        (1744830467u32, 476usize),
                        (1744830467u32, 477usize),
                        (1744830467u32, 478usize),
                        (1744830467u32, 479usize),
                        (1744830467u32, 480usize),
                        (1744830467u32, 481usize),
                        (1744830467u32, 482usize),
                        (1744830467u32, 483usize),
                        (1744830467u32, 484usize),
                        (1744830467u32, 485usize),
                        (1744830467u32, 486usize),
                        (1744830467u32, 487usize),
                        (1744830467u32, 488usize),
                        (1744830467u32, 489usize),
                        (1744830467u32, 490usize),
                        (1744830467u32, 491usize),
                        (1744830467u32, 492usize),
                    ];
                    let mut _g: usize = 0;
                    while _g < 352usize {
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
                    const CK_QUAD_GROUPS: [(usize, usize, usize); 301usize] = [
                        (0usize, 0usize, 1usize),
                        (2usize, 1usize, 1usize),
                        (3usize, 2usize, 1usize),
                        (4usize, 3usize, 1usize),
                        (5usize, 4usize, 2usize),
                        (6usize, 6usize, 1usize),
                        (7usize, 7usize, 2usize),
                        (8usize, 9usize, 1usize),
                        (9usize, 10usize, 2usize),
                        (10usize, 12usize, 1usize),
                        (11usize, 13usize, 2usize),
                        (12usize, 15usize, 1usize),
                        (13usize, 16usize, 2usize),
                        (14usize, 18usize, 1usize),
                        (15usize, 19usize, 2usize),
                        (16usize, 21usize, 1usize),
                        (17usize, 22usize, 2usize),
                        (18usize, 24usize, 1usize),
                        (19usize, 25usize, 2usize),
                        (20usize, 27usize, 1usize),
                        (21usize, 28usize, 2usize),
                        (22usize, 30usize, 1usize),
                        (23usize, 31usize, 2usize),
                        (24usize, 33usize, 1usize),
                        (25usize, 34usize, 2usize),
                        (26usize, 36usize, 1usize),
                        (27usize, 37usize, 2usize),
                        (28usize, 39usize, 1usize),
                        (29usize, 40usize, 2usize),
                        (30usize, 42usize, 1usize),
                        (31usize, 43usize, 2usize),
                        (32usize, 45usize, 1usize),
                        (33usize, 46usize, 2usize),
                        (34usize, 48usize, 1usize),
                        (35usize, 49usize, 2usize),
                        (36usize, 51usize, 1usize),
                        (37usize, 52usize, 1usize),
                        (38usize, 53usize, 1usize),
                        (39usize, 54usize, 1usize),
                        (40usize, 55usize, 1usize),
                        (41usize, 56usize, 1usize),
                        (42usize, 57usize, 1usize),
                        (43usize, 58usize, 1usize),
                        (44usize, 59usize, 1usize),
                        (45usize, 60usize, 1usize),
                        (46usize, 61usize, 1usize),
                        (47usize, 62usize, 1usize),
                        (48usize, 63usize, 3usize),
                        (49usize, 66usize, 3usize),
                        (50usize, 69usize, 3usize),
                        (51usize, 72usize, 3usize),
                        (52usize, 75usize, 1usize),
                        (53usize, 76usize, 1usize),
                        (54usize, 77usize, 3usize),
                        (55usize, 80usize, 3usize),
                        (56usize, 83usize, 3usize),
                        (57usize, 86usize, 3usize),
                        (58usize, 89usize, 3usize),
                        (59usize, 92usize, 3usize),
                        (60usize, 95usize, 3usize),
                        (61usize, 98usize, 3usize),
                        (62usize, 101usize, 3usize),
                        (63usize, 104usize, 3usize),
                        (64usize, 107usize, 3usize),
                        (65usize, 110usize, 3usize),
                        (66usize, 113usize, 3usize),
                        (67usize, 116usize, 3usize),
                        (68usize, 119usize, 3usize),
                        (69usize, 122usize, 3usize),
                        (70usize, 125usize, 3usize),
                        (71usize, 128usize, 3usize),
                        (72usize, 131usize, 3usize),
                        (73usize, 134usize, 3usize),
                        (74usize, 137usize, 3usize),
                        (75usize, 140usize, 3usize),
                        (76usize, 143usize, 3usize),
                        (77usize, 146usize, 3usize),
                        (78usize, 149usize, 3usize),
                        (79usize, 152usize, 3usize),
                        (80usize, 155usize, 3usize),
                        (81usize, 158usize, 3usize),
                        (82usize, 161usize, 3usize),
                        (83usize, 164usize, 3usize),
                        (84usize, 167usize, 3usize),
                        (85usize, 170usize, 3usize),
                        (86usize, 173usize, 10usize),
                        (87usize, 183usize, 10usize),
                        (88usize, 193usize, 10usize),
                        (89usize, 203usize, 10usize),
                        (90usize, 213usize, 10usize),
                        (91usize, 223usize, 10usize),
                        (92usize, 233usize, 10usize),
                        (93usize, 243usize, 10usize),
                        (94usize, 253usize, 10usize),
                        (95usize, 263usize, 10usize),
                        (96usize, 273usize, 10usize),
                        (97usize, 283usize, 10usize),
                        (98usize, 293usize, 10usize),
                        (99usize, 303usize, 10usize),
                        (100usize, 313usize, 10usize),
                        (101usize, 323usize, 10usize),
                        (102usize, 333usize, 10usize),
                        (103usize, 343usize, 10usize),
                        (104usize, 353usize, 10usize),
                        (105usize, 363usize, 10usize),
                        (106usize, 373usize, 10usize),
                        (107usize, 383usize, 10usize),
                        (108usize, 393usize, 10usize),
                        (109usize, 403usize, 10usize),
                        (110usize, 413usize, 10usize),
                        (111usize, 423usize, 10usize),
                        (112usize, 433usize, 10usize),
                        (113usize, 443usize, 10usize),
                        (114usize, 453usize, 10usize),
                        (115usize, 463usize, 10usize),
                        (116usize, 473usize, 10usize),
                        (117usize, 483usize, 10usize),
                        (153usize, 493usize, 3usize),
                        (155usize, 496usize, 3usize),
                        (157usize, 499usize, 3usize),
                        (159usize, 502usize, 3usize),
                        (161usize, 505usize, 3usize),
                        (163usize, 508usize, 3usize),
                        (165usize, 511usize, 3usize),
                        (167usize, 514usize, 3usize),
                        (169usize, 517usize, 3usize),
                        (171usize, 520usize, 3usize),
                        (173usize, 523usize, 3usize),
                        (175usize, 526usize, 3usize),
                        (177usize, 529usize, 3usize),
                        (179usize, 532usize, 3usize),
                        (181usize, 535usize, 3usize),
                        (183usize, 538usize, 3usize),
                        (184usize, 541usize, 1usize),
                        (185usize, 542usize, 1usize),
                        (186usize, 543usize, 1usize),
                        (187usize, 544usize, 1usize),
                        (188usize, 545usize, 1usize),
                        (189usize, 546usize, 1usize),
                        (190usize, 547usize, 1usize),
                        (191usize, 548usize, 1usize),
                        (192usize, 549usize, 1usize),
                        (193usize, 550usize, 1usize),
                        (194usize, 551usize, 1usize),
                        (195usize, 552usize, 1usize),
                        (196usize, 553usize, 1usize),
                        (197usize, 554usize, 1usize),
                        (198usize, 555usize, 1usize),
                        (199usize, 556usize, 1usize),
                        (200usize, 557usize, 1usize),
                        (201usize, 558usize, 1usize),
                        (202usize, 559usize, 1usize),
                        (203usize, 560usize, 1usize),
                        (204usize, 561usize, 1usize),
                        (205usize, 562usize, 1usize),
                        (206usize, 563usize, 1usize),
                        (207usize, 564usize, 1usize),
                        (208usize, 565usize, 1usize),
                        (209usize, 566usize, 1usize),
                        (210usize, 567usize, 1usize),
                        (211usize, 568usize, 1usize),
                        (212usize, 569usize, 1usize),
                        (213usize, 570usize, 1usize),
                        (214usize, 571usize, 1usize),
                        (215usize, 572usize, 1usize),
                        (216usize, 573usize, 1usize),
                        (217usize, 574usize, 1usize),
                        (218usize, 575usize, 1usize),
                        (219usize, 576usize, 1usize),
                        (220usize, 577usize, 1usize),
                        (221usize, 578usize, 1usize),
                        (222usize, 579usize, 1usize),
                        (223usize, 580usize, 1usize),
                        (224usize, 581usize, 1usize),
                        (225usize, 582usize, 1usize),
                        (226usize, 583usize, 1usize),
                        (227usize, 584usize, 1usize),
                        (228usize, 585usize, 1usize),
                        (229usize, 586usize, 1usize),
                        (230usize, 587usize, 1usize),
                        (231usize, 588usize, 1usize),
                        (232usize, 589usize, 1usize),
                        (233usize, 590usize, 1usize),
                        (234usize, 591usize, 1usize),
                        (235usize, 592usize, 1usize),
                        (236usize, 593usize, 1usize),
                        (237usize, 594usize, 1usize),
                        (238usize, 595usize, 1usize),
                        (239usize, 596usize, 1usize),
                        (240usize, 597usize, 1usize),
                        (241usize, 598usize, 1usize),
                        (242usize, 599usize, 1usize),
                        (243usize, 600usize, 1usize),
                        (244usize, 601usize, 1usize),
                        (245usize, 602usize, 1usize),
                        (246usize, 603usize, 1usize),
                        (247usize, 604usize, 1usize),
                        (248usize, 605usize, 1usize),
                        (249usize, 606usize, 1usize),
                        (250usize, 607usize, 1usize),
                        (251usize, 608usize, 1usize),
                        (252usize, 609usize, 1usize),
                        (253usize, 610usize, 1usize),
                        (254usize, 611usize, 1usize),
                        (255usize, 612usize, 1usize),
                        (256usize, 613usize, 1usize),
                        (257usize, 614usize, 1usize),
                        (258usize, 615usize, 1usize),
                        (259usize, 616usize, 1usize),
                        (260usize, 617usize, 1usize),
                        (261usize, 618usize, 1usize),
                        (262usize, 619usize, 1usize),
                        (263usize, 620usize, 1usize),
                        (264usize, 621usize, 1usize),
                        (265usize, 622usize, 1usize),
                        (266usize, 623usize, 1usize),
                        (267usize, 624usize, 1usize),
                        (268usize, 625usize, 1usize),
                        (269usize, 626usize, 1usize),
                        (270usize, 627usize, 1usize),
                        (271usize, 628usize, 1usize),
                        (272usize, 629usize, 1usize),
                        (273usize, 630usize, 1usize),
                        (274usize, 631usize, 1usize),
                        (275usize, 632usize, 1usize),
                        (276usize, 633usize, 1usize),
                        (277usize, 634usize, 1usize),
                        (278usize, 635usize, 1usize),
                        (279usize, 636usize, 1usize),
                        (280usize, 637usize, 1usize),
                        (281usize, 638usize, 1usize),
                        (282usize, 639usize, 1usize),
                        (283usize, 640usize, 1usize),
                        (284usize, 641usize, 1usize),
                        (285usize, 642usize, 1usize),
                        (286usize, 643usize, 1usize),
                        (287usize, 644usize, 1usize),
                        (288usize, 645usize, 1usize),
                        (289usize, 646usize, 1usize),
                        (290usize, 647usize, 1usize),
                        (291usize, 648usize, 1usize),
                        (292usize, 649usize, 1usize),
                        (293usize, 650usize, 1usize),
                        (294usize, 651usize, 1usize),
                        (295usize, 652usize, 1usize),
                        (296usize, 653usize, 1usize),
                        (297usize, 654usize, 1usize),
                        (298usize, 655usize, 1usize),
                        (299usize, 656usize, 1usize),
                        (300usize, 657usize, 1usize),
                        (301usize, 658usize, 1usize),
                        (302usize, 659usize, 1usize),
                        (303usize, 660usize, 1usize),
                        (304usize, 661usize, 1usize),
                        (305usize, 662usize, 1usize),
                        (306usize, 663usize, 1usize),
                        (307usize, 664usize, 1usize),
                        (308usize, 665usize, 1usize),
                        (309usize, 666usize, 1usize),
                        (310usize, 667usize, 1usize),
                        (311usize, 668usize, 1usize),
                        (312usize, 669usize, 1usize),
                        (313usize, 670usize, 1usize),
                        (314usize, 671usize, 1usize),
                        (315usize, 672usize, 1usize),
                        (316usize, 673usize, 1usize),
                        (317usize, 674usize, 1usize),
                        (318usize, 675usize, 1usize),
                        (319usize, 676usize, 1usize),
                        (320usize, 677usize, 1usize),
                        (321usize, 678usize, 1usize),
                        (322usize, 679usize, 1usize),
                        (323usize, 680usize, 1usize),
                        (324usize, 681usize, 1usize),
                        (325usize, 682usize, 1usize),
                        (326usize, 683usize, 1usize),
                        (327usize, 684usize, 1usize),
                        (328usize, 685usize, 1usize),
                        (329usize, 686usize, 1usize),
                        (330usize, 687usize, 1usize),
                        (331usize, 688usize, 1usize),
                        (332usize, 689usize, 1usize),
                        (333usize, 690usize, 1usize),
                        (334usize, 691usize, 1usize),
                        (335usize, 692usize, 1usize),
                        (336usize, 693usize, 1usize),
                        (337usize, 694usize, 1usize),
                        (338usize, 695usize, 1usize),
                        (339usize, 696usize, 1usize),
                        (340usize, 697usize, 1usize),
                        (341usize, 698usize, 1usize),
                        (342usize, 699usize, 1usize),
                        (343usize, 700usize, 1usize),
                        (344usize, 701usize, 1usize),
                        (345usize, 702usize, 1usize),
                        (346usize, 703usize, 1usize),
                        (347usize, 704usize, 1usize),
                        (348usize, 705usize, 1usize),
                        (349usize, 706usize, 1usize),
                        (350usize, 707usize, 1usize),
                        (351usize, 708usize, 1usize),
                    ];
                    const CK_QUAD_TERMS: [(u32, usize, usize); 709usize] = [
                        (268435454u32, 626usize, 626usize),
                        (268435454u32, 0usize, 9usize),
                        (1744830467u32, 2usize, 3usize),
                        (1744830467u32, 495usize, 2usize),
                        (268435454u32, 3usize, 15usize),
                        (1744830467u32, 527usize, 3usize),
                        (1744830467u32, 496usize, 2usize),
                        (268435454u32, 3usize, 17usize),
                        (1744830467u32, 528usize, 3usize),
                        (1744830467u32, 499usize, 2usize),
                        (268435454u32, 3usize, 19usize),
                        (1744830467u32, 531usize, 3usize),
                        (1744830467u32, 500usize, 2usize),
                        (268435454u32, 3usize, 21usize),
                        (1744830467u32, 532usize, 3usize),
                        (1744830467u32, 503usize, 2usize),
                        (268435454u32, 3usize, 23usize),
                        (1744830467u32, 535usize, 3usize),
                        (1744830467u32, 504usize, 2usize),
                        (268435454u32, 3usize, 25usize),
                        (1744830467u32, 536usize, 3usize),
                        (1744830467u32, 507usize, 2usize),
                        (268435454u32, 3usize, 27usize),
                        (1744830467u32, 539usize, 3usize),
                        (1744830467u32, 508usize, 2usize),
                        (268435454u32, 3usize, 29usize),
                        (1744830467u32, 540usize, 3usize),
                        (1744830467u32, 511usize, 2usize),
                        (268435454u32, 3usize, 31usize),
                        (1744830467u32, 543usize, 3usize),
                        (1744830467u32, 512usize, 2usize),
                        (268435454u32, 3usize, 33usize),
                        (1744830467u32, 544usize, 3usize),
                        (1744830467u32, 515usize, 2usize),
                        (268435454u32, 3usize, 35usize),
                        (1744830467u32, 547usize, 3usize),
                        (1744830467u32, 516usize, 2usize),
                        (268435454u32, 3usize, 37usize),
                        (1744830467u32, 548usize, 3usize),
                        (1744830467u32, 519usize, 2usize),
                        (268435454u32, 3usize, 39usize),
                        (1744830467u32, 551usize, 3usize),
                        (1744830467u32, 520usize, 2usize),
                        (268435454u32, 3usize, 41usize),
                        (1744830467u32, 552usize, 3usize),
                        (1744830467u32, 523usize, 2usize),
                        (268435454u32, 3usize, 43usize),
                        (1744830467u32, 555usize, 3usize),
                        (1744830467u32, 524usize, 2usize),
                        (268435454u32, 3usize, 45usize),
                        (1744830467u32, 556usize, 3usize),
                        (1744830467u32, 559usize, 3usize),
                        (1744830467u32, 560usize, 3usize),
                        (1744830467u32, 563usize, 3usize),
                        (1744830467u32, 564usize, 3usize),
                        (1744830467u32, 567usize, 3usize),
                        (1744830467u32, 568usize, 3usize),
                        (1744830467u32, 571usize, 3usize),
                        (1744830467u32, 572usize, 3usize),
                        (1744830467u32, 579usize, 3usize),
                        (1744830467u32, 580usize, 3usize),
                        (1744830467u32, 587usize, 3usize),
                        (1744830467u32, 588usize, 3usize),
                        (671043723u32, 2usize, 3usize),
                        (1744830467u32, 575usize, 3usize),
                        (268435454u32, 575usize, 14usize),
                        (1342133014u32, 2usize, 3usize),
                        (1744830467u32, 576usize, 3usize),
                        (268435454u32, 576usize, 14usize),
                        (536849980u32, 2usize, 3usize),
                        (1744830467u32, 583usize, 3usize),
                        (268435454u32, 583usize, 14usize),
                        (805183770u32, 2usize, 3usize),
                        (1744830467u32, 584usize, 3usize),
                        (268435454u32, 584usize, 14usize),
                        (268435454u32, 1usize, 2usize),
                        (1744830467u32, 1usize, 2usize),
                        (268435454u32, 495usize, 64usize),
                        (1744830467u32, 591usize, 2usize),
                        (268435454u32, 591usize, 63usize),
                        (268435454u32, 496usize, 64usize),
                        (1744830467u32, 592usize, 2usize),
                        (268435454u32, 592usize, 63usize),
                        (268435454u32, 499usize, 64usize),
                        (1744830467u32, 593usize, 2usize),
                        (268435454u32, 593usize, 63usize),
                        (268435454u32, 500usize, 64usize),
                        (1744830467u32, 594usize, 2usize),
                        (268435454u32, 594usize, 63usize),
                        (268435454u32, 503usize, 64usize),
                        (1744830467u32, 595usize, 2usize),
                        (268435454u32, 595usize, 63usize),
                        (268435454u32, 504usize, 64usize),
                        (1744830467u32, 596usize, 2usize),
                        (268435454u32, 596usize, 63usize),
                        (268435454u32, 507usize, 64usize),
                        (1744830467u32, 597usize, 2usize),
                        (268435454u32, 597usize, 63usize),
                        (268435454u32, 508usize, 64usize),
                        (1744830467u32, 598usize, 2usize),
                        (268435454u32, 598usize, 63usize),
                        (268435454u32, 511usize, 64usize),
                        (1744830467u32, 599usize, 2usize),
                        (268435454u32, 599usize, 63usize),
                        (268435454u32, 512usize, 64usize),
                        (1744830467u32, 600usize, 2usize),
                        (268435454u32, 600usize, 63usize),
                        (268435454u32, 515usize, 64usize),
                        (1744830467u32, 601usize, 2usize),
                        (268435454u32, 601usize, 63usize),
                        (268435454u32, 516usize, 64usize),
                        (1744830467u32, 602usize, 2usize),
                        (268435454u32, 602usize, 63usize),
                        (268435454u32, 519usize, 64usize),
                        (1744830467u32, 603usize, 2usize),
                        (268435454u32, 603usize, 63usize),
                        (268435454u32, 520usize, 64usize),
                        (1744830467u32, 604usize, 2usize),
                        (268435454u32, 604usize, 63usize),
                        (268435454u32, 523usize, 64usize),
                        (1744830467u32, 605usize, 2usize),
                        (268435454u32, 605usize, 63usize),
                        (268435454u32, 524usize, 64usize),
                        (1744830467u32, 606usize, 2usize),
                        (268435454u32, 606usize, 63usize),
                        (268435454u32, 495usize, 63usize),
                        (268435454u32, 591usize, 64usize),
                        (1744830467u32, 607usize, 2usize),
                        (268435454u32, 496usize, 63usize),
                        (268435454u32, 592usize, 64usize),
                        (1744830467u32, 608usize, 2usize),
                        (268435454u32, 499usize, 63usize),
                        (268435454u32, 593usize, 64usize),
                        (1744830467u32, 609usize, 2usize),
                        (268435454u32, 500usize, 63usize),
                        (268435454u32, 594usize, 64usize),
                        (1744830467u32, 610usize, 2usize),
                        (268435454u32, 503usize, 63usize),
                        (268435454u32, 595usize, 64usize),
                        (1744830467u32, 611usize, 2usize),
                        (268435454u32, 504usize, 63usize),
                        (268435454u32, 596usize, 64usize),
                        (1744830467u32, 612usize, 2usize),
                        (268435454u32, 507usize, 63usize),
                        (268435454u32, 597usize, 64usize),
                        (1744830467u32, 613usize, 2usize),
                        (268435454u32, 508usize, 63usize),
                        (268435454u32, 598usize, 64usize),
                        (1744830467u32, 614usize, 2usize),
                        (268435454u32, 511usize, 63usize),
                        (268435454u32, 599usize, 64usize),
                        (1744830467u32, 615usize, 2usize),
                        (268435454u32, 512usize, 63usize),
                        (268435454u32, 600usize, 64usize),
                        (1744830467u32, 616usize, 2usize),
                        (268435454u32, 515usize, 63usize),
                        (268435454u32, 601usize, 64usize),
                        (1744830467u32, 617usize, 2usize),
                        (268435454u32, 516usize, 63usize),
                        (268435454u32, 602usize, 64usize),
                        (1744830467u32, 618usize, 2usize),
                        (268435454u32, 519usize, 63usize),
                        (268435454u32, 603usize, 64usize),
                        (1744830467u32, 619usize, 2usize),
                        (268435454u32, 520usize, 63usize),
                        (268435454u32, 604usize, 64usize),
                        (1744830467u32, 620usize, 2usize),
                        (268435454u32, 523usize, 63usize),
                        (268435454u32, 605usize, 64usize),
                        (1744830467u32, 621usize, 2usize),
                        (268435454u32, 524usize, 63usize),
                        (268435454u32, 606usize, 64usize),
                        (1744830467u32, 622usize, 2usize),
                        (268435454u32, 3usize, 65usize),
                        (268435454u32, 4usize, 93usize),
                        (268435454u32, 5usize, 87usize),
                        (268435454u32, 6usize, 79usize),
                        (268435454u32, 7usize, 83usize),
                        (268435454u32, 8usize, 69usize),
                        (268435454u32, 9usize, 89usize),
                        (268435454u32, 10usize, 91usize),
                        (268435454u32, 11usize, 77usize),
                        (268435454u32, 12usize, 85usize),
                        (268435454u32, 3usize, 66usize),
                        (268435454u32, 4usize, 94usize),
                        (268435454u32, 5usize, 88usize),
                        (268435454u32, 6usize, 80usize),
                        (268435454u32, 7usize, 84usize),
                        (268435454u32, 8usize, 70usize),
                        (268435454u32, 9usize, 90usize),
                        (268435454u32, 10usize, 92usize),
                        (268435454u32, 11usize, 78usize),
                        (268435454u32, 12usize, 86usize),
                        (268435454u32, 3usize, 67usize),
                        (268435454u32, 4usize, 85usize),
                        (268435454u32, 5usize, 81usize),
                        (268435454u32, 6usize, 83usize),
                        (268435454u32, 7usize, 65usize),
                        (268435454u32, 8usize, 89usize),
                        (268435454u32, 9usize, 75usize),
                        (268435454u32, 10usize, 87usize),
                        (268435454u32, 11usize, 95usize),
                        (268435454u32, 12usize, 69usize),
                        (268435454u32, 3usize, 68usize),
                        (268435454u32, 4usize, 86usize),
                        (268435454u32, 5usize, 82usize),
                        (268435454u32, 6usize, 84usize),
                        (268435454u32, 7usize, 66usize),
                        (268435454u32, 8usize, 90usize),
                        (268435454u32, 9usize, 76usize),
                        (268435454u32, 10usize, 88usize),
                        (268435454u32, 11usize, 96usize),
                        (268435454u32, 12usize, 70usize),
                        (268435454u32, 3usize, 69usize),
                        (268435454u32, 4usize, 73usize),
                        (268435454u32, 5usize, 89usize),
                        (268435454u32, 6usize, 71usize),
                        (268435454u32, 7usize, 75usize),
                        (268435454u32, 8usize, 77usize),
                        (268435454u32, 9usize, 67usize),
                        (268435454u32, 10usize, 79usize),
                        (268435454u32, 11usize, 93usize),
                        (268435454u32, 12usize, 81usize),
                        (268435454u32, 3usize, 70usize),
                        (268435454u32, 4usize, 74usize),
                        (268435454u32, 5usize, 90usize),
                        (268435454u32, 6usize, 72usize),
                        (268435454u32, 7usize, 76usize),
                        (268435454u32, 8usize, 78usize),
                        (268435454u32, 9usize, 68usize),
                        (268435454u32, 10usize, 80usize),
                        (268435454u32, 11usize, 94usize),
                        (268435454u32, 12usize, 82usize),
                        (268435454u32, 3usize, 71usize),
                        (268435454u32, 4usize, 81usize),
                        (268435454u32, 5usize, 65usize),
                        (268435454u32, 6usize, 67usize),
                        (268435454u32, 7usize, 79usize),
                        (268435454u32, 8usize, 85usize),
                        (268435454u32, 9usize, 95usize),
                        (268435454u32, 10usize, 93usize),
                        (268435454u32, 11usize, 83usize),
                        (268435454u32, 12usize, 73usize),
                        (268435454u32, 3usize, 72usize),
                        (268435454u32, 4usize, 82usize),
                        (268435454u32, 5usize, 66usize),
                        (268435454u32, 6usize, 68usize),
                        (268435454u32, 7usize, 80usize),
                        (268435454u32, 8usize, 86usize),
                        (268435454u32, 9usize, 96usize),
                        (268435454u32, 10usize, 94usize),
                        (268435454u32, 11usize, 84usize),
                        (268435454u32, 12usize, 74usize),
                        (268435454u32, 3usize, 73usize),
                        (268435454u32, 4usize, 83usize),
                        (268435454u32, 5usize, 75usize),
                        (268435454u32, 6usize, 91usize),
                        (268435454u32, 7usize, 69usize),
                        (268435454u32, 8usize, 65usize),
                        (268435454u32, 9usize, 93usize),
                        (268435454u32, 10usize, 89usize),
                        (268435454u32, 11usize, 87usize),
                        (268435454u32, 12usize, 79usize),
                        (268435454u32, 3usize, 74usize),
                        (268435454u32, 4usize, 84usize),
                        (268435454u32, 5usize, 76usize),
                        (268435454u32, 6usize, 92usize),
                        (268435454u32, 7usize, 70usize),
                        (268435454u32, 8usize, 66usize),
                        (268435454u32, 9usize, 94usize),
                        (268435454u32, 10usize, 90usize),
                        (268435454u32, 11usize, 88usize),
                        (268435454u32, 12usize, 80usize),
                        (268435454u32, 3usize, 75usize),
                        (268435454u32, 4usize, 95usize),
                        (268435454u32, 5usize, 69usize),
                        (268435454u32, 6usize, 89usize),
                        (268435454u32, 7usize, 73usize),
                        (268435454u32, 8usize, 87usize),
                        (268435454u32, 9usize, 91usize),
                        (268435454u32, 10usize, 67usize),
                        (268435454u32, 11usize, 71usize),
                        (268435454u32, 12usize, 77usize),
                        (268435454u32, 3usize, 76usize),
                        (268435454u32, 4usize, 96usize),
                        (268435454u32, 5usize, 70usize),
                        (268435454u32, 6usize, 90usize),
                        (268435454u32, 7usize, 74usize),
                        (268435454u32, 8usize, 88usize),
                        (268435454u32, 9usize, 92usize),
                        (268435454u32, 10usize, 68usize),
                        (268435454u32, 11usize, 72usize),
                        (268435454u32, 12usize, 78usize),
                        (268435454u32, 3usize, 77usize),
                        (268435454u32, 4usize, 91usize),
                        (268435454u32, 5usize, 95usize),
                        (268435454u32, 6usize, 87usize),
                        (268435454u32, 7usize, 85usize),
                        (268435454u32, 8usize, 81usize),
                        (268435454u32, 9usize, 73usize),
                        (268435454u32, 10usize, 71usize),
                        (268435454u32, 11usize, 65usize),
                        (268435454u32, 12usize, 67usize),
                        (268435454u32, 3usize, 78usize),
                        (268435454u32, 4usize, 92usize),
                        (268435454u32, 5usize, 96usize),
                        (268435454u32, 6usize, 88usize),
                        (268435454u32, 7usize, 86usize),
                        (268435454u32, 8usize, 82usize),
                        (268435454u32, 9usize, 74usize),
                        (268435454u32, 10usize, 72usize),
                        (268435454u32, 11usize, 66usize),
                        (268435454u32, 12usize, 68usize),
                        (268435454u32, 3usize, 79usize),
                        (268435454u32, 4usize, 77usize),
                        (268435454u32, 5usize, 91usize),
                        (268435454u32, 6usize, 93usize),
                        (268435454u32, 7usize, 95usize),
                        (268435454u32, 8usize, 71usize),
                        (268435454u32, 9usize, 85usize),
                        (268435454u32, 10usize, 83usize),
                        (268435454u32, 11usize, 81usize),
                        (268435454u32, 12usize, 75usize),
                        (268435454u32, 3usize, 80usize),
                        (268435454u32, 4usize, 78usize),
                        (268435454u32, 5usize, 92usize),
                        (268435454u32, 6usize, 94usize),
                        (268435454u32, 7usize, 96usize),
                        (268435454u32, 8usize, 72usize),
                        (268435454u32, 9usize, 86usize),
                        (268435454u32, 10usize, 84usize),
                        (268435454u32, 11usize, 82usize),
                        (268435454u32, 12usize, 76usize),
                        (268435454u32, 3usize, 81usize),
                        (268435454u32, 4usize, 67usize),
                        (268435454u32, 5usize, 85usize),
                        (268435454u32, 6usize, 69usize),
                        (268435454u32, 7usize, 93usize),
                        (268435454u32, 8usize, 73usize),
                        (268435454u32, 9usize, 65usize),
                        (268435454u32, 10usize, 75usize),
                        (268435454u32, 11usize, 89usize),
                        (268435454u32, 12usize, 95usize),
                        (268435454u32, 3usize, 82usize),
                        (268435454u32, 4usize, 68usize),
                        (268435454u32, 5usize, 86usize),
                        (268435454u32, 6usize, 70usize),
                        (268435454u32, 7usize, 94usize),
                        (268435454u32, 8usize, 74usize),
                        (268435454u32, 9usize, 66usize),
                        (268435454u32, 10usize, 76usize),
                        (268435454u32, 11usize, 90usize),
                        (268435454u32, 12usize, 96usize),
                        (268435454u32, 3usize, 83usize),
                        (268435454u32, 4usize, 89usize),
                        (268435454u32, 5usize, 93usize),
                        (268435454u32, 6usize, 77usize),
                        (268435454u32, 7usize, 67usize),
                        (268435454u32, 8usize, 91usize),
                        (268435454u32, 9usize, 79usize),
                        (268435454u32, 10usize, 65usize),
                        (268435454u32, 11usize, 69usize),
                        (268435454u32, 12usize, 87usize),
                        (268435454u32, 3usize, 84usize),
                        (268435454u32, 4usize, 90usize),
                        (268435454u32, 5usize, 94usize),
                        (268435454u32, 6usize, 78usize),
                        (268435454u32, 7usize, 68usize),
                        (268435454u32, 8usize, 92usize),
                        (268435454u32, 9usize, 80usize),
                        (268435454u32, 10usize, 66usize),
                        (268435454u32, 11usize, 70usize),
                        (268435454u32, 12usize, 88usize),
                        (268435454u32, 3usize, 85usize),
                        (268435454u32, 4usize, 65usize),
                        (268435454u32, 5usize, 71usize),
                        (268435454u32, 6usize, 75usize),
                        (268435454u32, 7usize, 87usize),
                        (268435454u32, 8usize, 79usize),
                        (268435454u32, 9usize, 77usize),
                        (268435454u32, 10usize, 95usize),
                        (268435454u32, 11usize, 91usize),
                        (268435454u32, 12usize, 83usize),
                        (268435454u32, 3usize, 86usize),
                        (268435454u32, 4usize, 66usize),
                        (268435454u32, 5usize, 72usize),
                        (268435454u32, 6usize, 76usize),
                        (268435454u32, 7usize, 88usize),
                        (268435454u32, 8usize, 80usize),
                        (268435454u32, 9usize, 78usize),
                        (268435454u32, 10usize, 96usize),
                        (268435454u32, 11usize, 92usize),
                        (268435454u32, 12usize, 84usize),
                        (268435454u32, 3usize, 87usize),
                        (268435454u32, 4usize, 69usize),
                        (268435454u32, 5usize, 77usize),
                        (268435454u32, 6usize, 85usize),
                        (268435454u32, 7usize, 89usize),
                        (268435454u32, 8usize, 75usize),
                        (268435454u32, 9usize, 71usize),
                        (268435454u32, 10usize, 73usize),
                        (268435454u32, 11usize, 79usize),
                        (268435454u32, 12usize, 93usize),
                        (268435454u32, 3usize, 88usize),
                        (268435454u32, 4usize, 70usize),
                        (268435454u32, 5usize, 78usize),
                        (268435454u32, 6usize, 86usize),
                        (268435454u32, 7usize, 90usize),
                        (268435454u32, 8usize, 76usize),
                        (268435454u32, 9usize, 72usize),
                        (268435454u32, 10usize, 74usize),
                        (268435454u32, 11usize, 80usize),
                        (268435454u32, 12usize, 94usize),
                        (268435454u32, 3usize, 89usize),
                        (268435454u32, 4usize, 87usize),
                        (268435454u32, 5usize, 79usize),
                        (268435454u32, 6usize, 73usize),
                        (268435454u32, 7usize, 77usize),
                        (268435454u32, 8usize, 95usize),
                        (268435454u32, 9usize, 83usize),
                        (268435454u32, 10usize, 81usize),
                        (268435454u32, 11usize, 67usize),
                        (268435454u32, 12usize, 71usize),
                        (268435454u32, 3usize, 90usize),
                        (268435454u32, 4usize, 88usize),
                        (268435454u32, 5usize, 80usize),
                        (268435454u32, 6usize, 74usize),
                        (268435454u32, 7usize, 78usize),
                        (268435454u32, 8usize, 96usize),
                        (268435454u32, 9usize, 84usize),
                        (268435454u32, 10usize, 82usize),
                        (268435454u32, 11usize, 68usize),
                        (268435454u32, 12usize, 72usize),
                        (268435454u32, 3usize, 91usize),
                        (268435454u32, 4usize, 79usize),
                        (268435454u32, 5usize, 67usize),
                        (268435454u32, 6usize, 65usize),
                        (268435454u32, 7usize, 81usize),
                        (268435454u32, 8usize, 93usize),
                        (268435454u32, 9usize, 69usize),
                        (268435454u32, 10usize, 77usize),
                        (268435454u32, 11usize, 73usize),
                        (268435454u32, 12usize, 89usize),
                        (268435454u32, 3usize, 92usize),
                        (268435454u32, 4usize, 80usize),
                        (268435454u32, 5usize, 68usize),
                        (268435454u32, 6usize, 66usize),
                        (268435454u32, 7usize, 82usize),
                        (268435454u32, 8usize, 94usize),
                        (268435454u32, 9usize, 70usize),
                        (268435454u32, 10usize, 78usize),
                        (268435454u32, 11usize, 74usize),
                        (268435454u32, 12usize, 90usize),
                        (268435454u32, 3usize, 93usize),
                        (268435454u32, 4usize, 75usize),
                        (268435454u32, 5usize, 83usize),
                        (268435454u32, 6usize, 95usize),
                        (268435454u32, 7usize, 71usize),
                        (268435454u32, 8usize, 67usize),
                        (268435454u32, 9usize, 81usize),
                        (268435454u32, 10usize, 69usize),
                        (268435454u32, 11usize, 85usize),
                        (268435454u32, 12usize, 91usize),
                        (268435454u32, 3usize, 94usize),
                        (268435454u32, 4usize, 76usize),
                        (268435454u32, 5usize, 84usize),
                        (268435454u32, 6usize, 96usize),
                        (268435454u32, 7usize, 72usize),
                        (268435454u32, 8usize, 68usize),
                        (268435454u32, 9usize, 82usize),
                        (268435454u32, 10usize, 70usize),
                        (268435454u32, 11usize, 86usize),
                        (268435454u32, 12usize, 92usize),
                        (268435454u32, 3usize, 95usize),
                        (268435454u32, 4usize, 71usize),
                        (268435454u32, 5usize, 73usize),
                        (268435454u32, 6usize, 81usize),
                        (268435454u32, 7usize, 91usize),
                        (268435454u32, 8usize, 83usize),
                        (268435454u32, 9usize, 87usize),
                        (268435454u32, 10usize, 85usize),
                        (268435454u32, 11usize, 75usize),
                        (268435454u32, 12usize, 65usize),
                        (268435454u32, 3usize, 96usize),
                        (268435454u32, 4usize, 72usize),
                        (268435454u32, 5usize, 74usize),
                        (268435454u32, 6usize, 82usize),
                        (268435454u32, 7usize, 92usize),
                        (268435454u32, 8usize, 84usize),
                        (268435454u32, 9usize, 88usize),
                        (268435454u32, 10usize, 86usize),
                        (268435454u32, 11usize, 76usize),
                        (268435454u32, 12usize, 66usize),
                        (268435454u32, 13usize, 379usize),
                        (134217455u32, 13usize, 380usize),
                        (1744830467u32, 495usize, 13usize),
                        (268435454u32, 13usize, 383usize),
                        (134217455u32, 13usize, 384usize),
                        (1744830467u32, 496usize, 13usize),
                        (268435454u32, 13usize, 387usize),
                        (134217455u32, 13usize, 388usize),
                        (1744830467u32, 499usize, 13usize),
                        (268435454u32, 13usize, 391usize),
                        (134217455u32, 13usize, 392usize),
                        (1744830467u32, 500usize, 13usize),
                        (268435454u32, 13usize, 395usize),
                        (134217455u32, 13usize, 396usize),
                        (1744830467u32, 503usize, 13usize),
                        (268435454u32, 13usize, 399usize),
                        (134217455u32, 13usize, 400usize),
                        (1744830467u32, 504usize, 13usize),
                        (268435454u32, 13usize, 403usize),
                        (134217455u32, 13usize, 404usize),
                        (1744830467u32, 507usize, 13usize),
                        (268435454u32, 13usize, 407usize),
                        (134217455u32, 13usize, 408usize),
                        (1744830467u32, 508usize, 13usize),
                        (268435454u32, 13usize, 412usize),
                        (268434910u32, 13usize, 413usize),
                        (1744830467u32, 511usize, 13usize),
                        (268435454u32, 13usize, 417usize),
                        (268434910u32, 13usize, 418usize),
                        (1744830467u32, 512usize, 13usize),
                        (268435454u32, 13usize, 422usize),
                        (268434910u32, 13usize, 423usize),
                        (1744830467u32, 515usize, 13usize),
                        (268435454u32, 13usize, 427usize),
                        (268434910u32, 13usize, 428usize),
                        (1744830467u32, 516usize, 13usize),
                        (268435454u32, 13usize, 432usize),
                        (268434910u32, 13usize, 433usize),
                        (1744830467u32, 519usize, 13usize),
                        (268435454u32, 13usize, 437usize),
                        (268434910u32, 13usize, 438usize),
                        (1744830467u32, 520usize, 13usize),
                        (268435454u32, 13usize, 442usize),
                        (268434910u32, 13usize, 443usize),
                        (1744830467u32, 523usize, 13usize),
                        (268435454u32, 13usize, 448usize),
                        (268434910u32, 13usize, 449usize),
                        (1744830467u32, 524usize, 13usize),
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
                        (268435454u32, 129usize, 129usize),
                        (268435454u32, 130usize, 130usize),
                        (268435454u32, 131usize, 131usize),
                        (268435454u32, 132usize, 132usize),
                        (268435454u32, 137usize, 137usize),
                        (268435454u32, 138usize, 138usize),
                        (268435454u32, 145usize, 145usize),
                        (268435454u32, 146usize, 146usize),
                        (268435454u32, 147usize, 147usize),
                        (268435454u32, 148usize, 148usize),
                        (268435454u32, 153usize, 153usize),
                        (268435454u32, 154usize, 154usize),
                        (268435454u32, 159usize, 159usize),
                        (268435454u32, 160usize, 160usize),
                        (268435454u32, 161usize, 161usize),
                        (268435454u32, 162usize, 162usize),
                        (268435454u32, 167usize, 167usize),
                        (268435454u32, 168usize, 168usize),
                        (268435454u32, 175usize, 175usize),
                        (268435454u32, 176usize, 176usize),
                        (268435454u32, 177usize, 177usize),
                        (268435454u32, 178usize, 178usize),
                        (268435454u32, 183usize, 183usize),
                        (268435454u32, 184usize, 184usize),
                        (268435454u32, 189usize, 189usize),
                        (268435454u32, 190usize, 190usize),
                        (268435454u32, 191usize, 191usize),
                        (268435454u32, 192usize, 192usize),
                        (268435454u32, 197usize, 197usize),
                        (268435454u32, 198usize, 198usize),
                        (268435454u32, 205usize, 205usize),
                        (268435454u32, 206usize, 206usize),
                        (268435454u32, 207usize, 207usize),
                        (268435454u32, 208usize, 208usize),
                        (268435454u32, 213usize, 213usize),
                        (268435454u32, 214usize, 214usize),
                        (268435454u32, 219usize, 219usize),
                        (268435454u32, 220usize, 220usize),
                        (268435454u32, 221usize, 221usize),
                        (268435454u32, 222usize, 222usize),
                        (268435454u32, 227usize, 227usize),
                        (268435454u32, 228usize, 228usize),
                        (268435454u32, 235usize, 235usize),
                        (268435454u32, 236usize, 236usize),
                        (268435454u32, 237usize, 237usize),
                        (268435454u32, 238usize, 238usize),
                        (268435454u32, 243usize, 243usize),
                        (268435454u32, 244usize, 244usize),
                        (268435454u32, 249usize, 249usize),
                        (268435454u32, 250usize, 250usize),
                        (268435454u32, 251usize, 251usize),
                        (268435454u32, 252usize, 252usize),
                        (268435454u32, 257usize, 257usize),
                        (268435454u32, 258usize, 258usize),
                        (268435454u32, 265usize, 265usize),
                        (268435454u32, 266usize, 266usize),
                        (268435454u32, 267usize, 267usize),
                        (268435454u32, 268usize, 268usize),
                        (268435454u32, 275usize, 275usize),
                        (268435454u32, 276usize, 276usize),
                        (268435454u32, 281usize, 281usize),
                        (268435454u32, 282usize, 282usize),
                        (268435454u32, 283usize, 283usize),
                        (268435454u32, 284usize, 284usize),
                        (268435454u32, 289usize, 289usize),
                        (268435454u32, 290usize, 290usize),
                        (268435454u32, 297usize, 297usize),
                        (268435454u32, 298usize, 298usize),
                        (268435454u32, 299usize, 299usize),
                        (268435454u32, 300usize, 300usize),
                        (268435454u32, 307usize, 307usize),
                        (268435454u32, 308usize, 308usize),
                        (268435454u32, 313usize, 313usize),
                        (268435454u32, 314usize, 314usize),
                        (268435454u32, 315usize, 315usize),
                        (268435454u32, 316usize, 316usize),
                        (268435454u32, 321usize, 321usize),
                        (268435454u32, 322usize, 322usize),
                        (268435454u32, 329usize, 329usize),
                        (268435454u32, 330usize, 330usize),
                        (268435454u32, 331usize, 331usize),
                        (268435454u32, 332usize, 332usize),
                        (268435454u32, 339usize, 339usize),
                        (268435454u32, 340usize, 340usize),
                        (268435454u32, 345usize, 345usize),
                        (268435454u32, 346usize, 346usize),
                        (268435454u32, 347usize, 347usize),
                        (268435454u32, 348usize, 348usize),
                        (268435454u32, 353usize, 353usize),
                        (268435454u32, 354usize, 354usize),
                        (268435454u32, 361usize, 361usize),
                        (268435454u32, 362usize, 362usize),
                        (268435454u32, 363usize, 363usize),
                        (268435454u32, 364usize, 364usize),
                        (268435454u32, 371usize, 371usize),
                        (268435454u32, 372usize, 372usize),
                        (268435454u32, 378usize, 378usize),
                        (268435454u32, 382usize, 382usize),
                        (268435454u32, 386usize, 386usize),
                        (268435454u32, 390usize, 390usize),
                        (268435454u32, 394usize, 394usize),
                        (268435454u32, 398usize, 398usize),
                        (268435454u32, 402usize, 402usize),
                        (268435454u32, 406usize, 406usize),
                        (268435454u32, 411usize, 411usize),
                        (268435454u32, 416usize, 416usize),
                        (268435454u32, 421usize, 421usize),
                        (268435454u32, 426usize, 426usize),
                        (268435454u32, 431usize, 431usize),
                        (268435454u32, 436usize, 436usize),
                        (268435454u32, 441usize, 441usize),
                        (268435454u32, 447usize, 447usize),
                        (268435454u32, 450usize, 450usize),
                        (268435454u32, 451usize, 451usize),
                        (268435454u32, 452usize, 452usize),
                        (268435454u32, 453usize, 453usize),
                        (268435454u32, 454usize, 454usize),
                        (268435454u32, 455usize, 455usize),
                        (268435454u32, 456usize, 456usize),
                        (268435454u32, 457usize, 457usize),
                        (268435454u32, 458usize, 458usize),
                        (268435454u32, 459usize, 459usize),
                        (268435454u32, 460usize, 460usize),
                        (268435454u32, 461usize, 461usize),
                        (268435454u32, 462usize, 462usize),
                        (268435454u32, 463usize, 463usize),
                        (268435454u32, 464usize, 464usize),
                        (268435454u32, 465usize, 465usize),
                        (268435454u32, 466usize, 466usize),
                        (268435454u32, 467usize, 467usize),
                        (268435454u32, 468usize, 468usize),
                        (268435454u32, 469usize, 469usize),
                        (268435454u32, 470usize, 470usize),
                        (268435454u32, 471usize, 471usize),
                        (268435454u32, 472usize, 472usize),
                        (268435454u32, 473usize, 473usize),
                        (268435454u32, 474usize, 474usize),
                        (268435454u32, 475usize, 475usize),
                        (268435454u32, 476usize, 476usize),
                        (268435454u32, 477usize, 477usize),
                        (268435454u32, 478usize, 478usize),
                        (268435454u32, 479usize, 479usize),
                        (268435454u32, 480usize, 480usize),
                        (268435454u32, 481usize, 481usize),
                        (268435454u32, 482usize, 482usize),
                        (268435454u32, 483usize, 483usize),
                        (268435454u32, 484usize, 484usize),
                        (268435454u32, 485usize, 485usize),
                        (268435454u32, 486usize, 486usize),
                        (268435454u32, 487usize, 487usize),
                        (268435454u32, 488usize, 488usize),
                        (268435454u32, 489usize, 489usize),
                        (268435454u32, 490usize, 490usize),
                        (268435454u32, 491usize, 491usize),
                        (268435454u32, 492usize, 492usize),
                    ];
                    let mut _g: usize = 0;
                    while _g < 301usize {
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
#[allow(clippy::needless_borrow)]
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
#[allow(clippy::needless_borrow)]
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
#[allow(clippy::needless_borrow)]
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
#[allow(clippy::needless_borrow)]
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
#[allow(clippy::needless_borrow)]
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
#[allow(
    unused_variables,
    unused_mut,
    clippy::needless_borrow,
    clippy::needless_range_loop,
    clippy::large_const_arrays
)]
unsafe fn layer_6_final_step_accumulator(
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
#[allow(clippy::needless_borrow)]
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
#[allow(
    unused_variables,
    unused_mut,
    clippy::needless_borrow,
    clippy::needless_range_loop,
    clippy::large_const_arrays
)]
unsafe fn layer_7_final_step_accumulator(
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
                _ => unreachable!(),
            }
            _sg += 1;
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
        {
            let mut i = 0;
            while i < GKR_TRANSCRIPT_U32 {
                transcript_buf.push(I::read_word());
                i += 1;
            }
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
        draw_field_els_into::<DRAW_BUF_CAPACITY>(
            &mut hasher,
            &mut seed,
            init_challenges.as_mut_slice(),
        );
        let lookup_alpha = *init_challenges.get(0);
        let lookup_additive_challenge = *init_challenges.get(1);
        let constraints_batch_challenge = *init_challenges.get(2);
        let mut evals_commit_buf = CommitBuf::<GKR_EVALS_COMMIT_BUF>::new();
        let evals_data_words = 96usize * EXT_DEGREE;
        {
            let mut i = 0;
            while i < evals_data_words {
                evals_commit_buf.data_write(i, read_reduced_field_el::<I>());
                i += 1;
            }
        }
        evals_commit_buf.commit(&mut hasher, &mut seed, evals_data_words);
        let evals_slice: &[BabyBearExt4] = unsafe { evals_commit_buf.data_as(96usize) };
        let mut all_challenges = LazyVec::<BabyBearExt4, { GKR_ROUNDS + 1 }>::new();
        unsafe {
            all_challenges.set_len(5usize);
        }
        draw_field_els_into::<DRAW_BUF_CAPACITY>(
            &mut hasher,
            &mut seed,
            all_challenges.as_mut_slice(),
        );
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
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_23_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    23usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_22_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    22usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_21_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    21usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_20_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    20usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_19_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    19usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_18_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    18usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_17_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    17usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_16_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    16usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_15_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    15usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_14_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    14usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_13_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    13usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_12_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    12usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_11_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    11usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_10_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    10usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_9_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    9usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
                    i += 1;
                }
            }
            {
                let evals: &[[BabyBearExt4; 4]] = eval_buf.data_as(6usize);
                let f = dim_reducing_8_final_step_accumulator(evals, state.batching_challenge);
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    8usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 3>::new();
            unsafe {
                draw_buf.set_len(3);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
                verify_sumcheck_rounds::<I, 19usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    7usize,
                )?;
            let mut fc_len = 19usize;
            let data_words = 8usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
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
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    7usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
                verify_sumcheck_rounds::<I, 19usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    6usize,
                )?;
            let mut fc_len = 19usize;
            let data_words = 15usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
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
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    6usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
                verify_sumcheck_rounds::<I, 19usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    5usize,
                )?;
            let mut fc_len = 19usize;
            let data_words = 25usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
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
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    5usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
                verify_sumcheck_rounds::<I, 19usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    4usize,
                )?;
            let mut fc_len = 19usize;
            let data_words = 47usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
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
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    4usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
                verify_sumcheck_rounds::<I, 19usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    3usize,
                )?;
            let mut fc_len = 19usize;
            let data_words = 91usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
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
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    3usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
                verify_sumcheck_rounds::<I, 19usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    2usize,
                )?;
            let mut fc_len = 19usize;
            let data_words = 175usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
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
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    2usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
                verify_sumcheck_rounds::<I, 19usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    1usize,
                )?;
            let mut fc_len = 19usize;
            let data_words = 343usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
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
                );
                verify_final_step_check(
                    f,
                    *state.prev_point.get_unchecked(state.prev_point_len - 1),
                    final_eq_prefactor,
                    final_claim,
                    1usize,
                )?;
            }
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
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
                verify_sumcheck_rounds::<I, 19usize, GKR_COMMIT_BUF>(
                    &mut seed,
                    initial_claim,
                    &mut state.prev_point,
                    0usize,
                )?;
            let mut fc_len = 19usize;
            let data_words =
                1012usize * 2 * <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
            {
                let mut i = 0;
                while i < data_words {
                    eval_buf.data_write(i, I::read_word());
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
            eval_buf.commit(&mut hasher, &mut seed, data_words);
            let mut draw_buf = LazyVec::<BabyBearExt4, 2>::new();
            unsafe {
                draw_buf.set_len(2);
            }
            draw_field_els_into::<DRAW_BUF_CAPACITY>(
                &mut hasher,
                &mut seed,
                draw_buf.as_mut_slice(),
            );
            let last_r = *draw_buf.get(0);
            let next_batching = *draw_buf.get(1);
            *state.prev_point.get_unchecked_mut(fc_len) = last_r;
            fc_len += 1;
            const EXTRA_COMMIT_BUF: usize = 992usize;
            let mut extra_buf = CommitBuf::<EXTRA_COMMIT_BUF>::new();
            let extra_data_words = 246usize * EXT_DEGREE;
            {
                let mut i = 0;
                while i < extra_data_words {
                    extra_buf.data_write(i, read_reduced_field_el::<I>());
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
            extra_buf.commit(&mut hasher, &mut seed, extra_data_words);
            let final_step_evals: &[[BabyBearExt4; 2]] = unsafe { eval_buf.data_as(1012usize) };
            state.prev_claims.clear();
            {
                const EXTRA_POS: [(usize, usize); 246usize] = [
                    (133usize, 0usize),
                    (134usize, 1usize),
                    (135usize, 2usize),
                    (138usize, 3usize),
                    (143usize, 4usize),
                    (144usize, 5usize),
                    (145usize, 6usize),
                    (146usize, 7usize),
                    (147usize, 8usize),
                    (148usize, 9usize),
                    (152usize, 10usize),
                    (153usize, 11usize),
                    (161usize, 12usize),
                    (162usize, 13usize),
                    (169usize, 14usize),
                    (170usize, 15usize),
                    (179usize, 16usize),
                    (180usize, 17usize),
                    (181usize, 18usize),
                    (184usize, 19usize),
                    (189usize, 20usize),
                    (190usize, 21usize),
                    (191usize, 22usize),
                    (192usize, 23usize),
                    (193usize, 24usize),
                    (194usize, 25usize),
                    (198usize, 26usize),
                    (199usize, 27usize),
                    (207usize, 28usize),
                    (208usize, 29usize),
                    (215usize, 30usize),
                    (216usize, 31usize),
                    (225usize, 32usize),
                    (226usize, 33usize),
                    (227usize, 34usize),
                    (230usize, 35usize),
                    (235usize, 36usize),
                    (236usize, 37usize),
                    (237usize, 38usize),
                    (238usize, 39usize),
                    (239usize, 40usize),
                    (240usize, 41usize),
                    (244usize, 42usize),
                    (245usize, 43usize),
                    (253usize, 44usize),
                    (254usize, 45usize),
                    (261usize, 46usize),
                    (262usize, 47usize),
                    (271usize, 48usize),
                    (272usize, 49usize),
                    (273usize, 50usize),
                    (276usize, 51usize),
                    (281usize, 52usize),
                    (282usize, 53usize),
                    (283usize, 54usize),
                    (284usize, 55usize),
                    (285usize, 56usize),
                    (286usize, 57usize),
                    (290usize, 58usize),
                    (291usize, 59usize),
                    (299usize, 60usize),
                    (300usize, 61usize),
                    (307usize, 62usize),
                    (308usize, 63usize),
                    (317usize, 64usize),
                    (318usize, 65usize),
                    (325usize, 66usize),
                    (326usize, 67usize),
                    (327usize, 68usize),
                    (328usize, 69usize),
                    (329usize, 70usize),
                    (330usize, 71usize),
                    (334usize, 72usize),
                    (335usize, 73usize),
                    (351usize, 74usize),
                    (352usize, 75usize),
                    (361usize, 76usize),
                    (362usize, 77usize),
                    (369usize, 78usize),
                    (370usize, 79usize),
                    (371usize, 80usize),
                    (372usize, 81usize),
                    (373usize, 82usize),
                    (374usize, 83usize),
                    (378usize, 84usize),
                    (379usize, 85usize),
                    (395usize, 86usize),
                    (396usize, 87usize),
                    (405usize, 88usize),
                    (406usize, 89usize),
                    (413usize, 90usize),
                    (414usize, 91usize),
                    (415usize, 92usize),
                    (416usize, 93usize),
                    (417usize, 94usize),
                    (418usize, 95usize),
                    (422usize, 96usize),
                    (423usize, 97usize),
                    (439usize, 98usize),
                    (440usize, 99usize),
                    (449usize, 100usize),
                    (450usize, 101usize),
                    (457usize, 102usize),
                    (458usize, 103usize),
                    (459usize, 104usize),
                    (460usize, 105usize),
                    (461usize, 106usize),
                    (462usize, 107usize),
                    (466usize, 108usize),
                    (467usize, 109usize),
                    (483usize, 110usize),
                    (484usize, 111usize),
                    (489usize, 112usize),
                    (490usize, 113usize),
                    (491usize, 114usize),
                    (496usize, 115usize),
                    (497usize, 116usize),
                    (498usize, 117usize),
                    (503usize, 118usize),
                    (504usize, 119usize),
                    (505usize, 120usize),
                    (510usize, 121usize),
                    (511usize, 122usize),
                    (512usize, 123usize),
                    (517usize, 124usize),
                    (518usize, 125usize),
                    (519usize, 126usize),
                    (524usize, 127usize),
                    (525usize, 128usize),
                    (526usize, 129usize),
                    (531usize, 130usize),
                    (532usize, 131usize),
                    (533usize, 132usize),
                    (538usize, 133usize),
                    (539usize, 134usize),
                    (540usize, 135usize),
                    (545usize, 136usize),
                    (547usize, 137usize),
                    (552usize, 138usize),
                    (554usize, 139usize),
                    (559usize, 140usize),
                    (561usize, 141usize),
                    (566usize, 142usize),
                    (568usize, 143usize),
                    (573usize, 144usize),
                    (575usize, 145usize),
                    (580usize, 146usize),
                    (582usize, 147usize),
                    (587usize, 148usize),
                    (589usize, 149usize),
                    (594usize, 150usize),
                    (646usize, 151usize),
                    (647usize, 152usize),
                    (648usize, 153usize),
                    (649usize, 154usize),
                    (650usize, 155usize),
                    (651usize, 156usize),
                    (656usize, 157usize),
                    (657usize, 158usize),
                    (662usize, 159usize),
                    (663usize, 160usize),
                    (668usize, 161usize),
                    (669usize, 162usize),
                    (674usize, 163usize),
                    (675usize, 164usize),
                    (680usize, 165usize),
                    (681usize, 166usize),
                    (686usize, 167usize),
                    (687usize, 168usize),
                    (692usize, 169usize),
                    (693usize, 170usize),
                    (698usize, 171usize),
                    (699usize, 172usize),
                    (704usize, 173usize),
                    (705usize, 174usize),
                    (710usize, 175usize),
                    (711usize, 176usize),
                    (716usize, 177usize),
                    (717usize, 178usize),
                    (722usize, 179usize),
                    (723usize, 180usize),
                    (728usize, 181usize),
                    (729usize, 182usize),
                    (734usize, 183usize),
                    (735usize, 184usize),
                    (740usize, 185usize),
                    (741usize, 186usize),
                    (746usize, 187usize),
                    (747usize, 188usize),
                    (752usize, 189usize),
                    (753usize, 190usize),
                    (758usize, 191usize),
                    (759usize, 192usize),
                    (764usize, 193usize),
                    (765usize, 194usize),
                    (770usize, 195usize),
                    (771usize, 196usize),
                    (776usize, 197usize),
                    (777usize, 198usize),
                    (782usize, 199usize),
                    (783usize, 200usize),
                    (788usize, 201usize),
                    (789usize, 202usize),
                    (794usize, 203usize),
                    (795usize, 204usize),
                    (796usize, 205usize),
                    (797usize, 206usize),
                    (798usize, 207usize),
                    (799usize, 208usize),
                    (802usize, 209usize),
                    (803usize, 210usize),
                    (806usize, 211usize),
                    (807usize, 212usize),
                    (810usize, 213usize),
                    (811usize, 214usize),
                    (814usize, 215usize),
                    (815usize, 216usize),
                    (818usize, 217usize),
                    (819usize, 218usize),
                    (822usize, 219usize),
                    (823usize, 220usize),
                    (826usize, 221usize),
                    (827usize, 222usize),
                    (830usize, 223usize),
                    (831usize, 224usize),
                    (834usize, 225usize),
                    (835usize, 226usize),
                    (838usize, 227usize),
                    (839usize, 228usize),
                    (842usize, 229usize),
                    (843usize, 230usize),
                    (846usize, 231usize),
                    (847usize, 232usize),
                    (850usize, 233usize),
                    (851usize, 234usize),
                    (854usize, 235usize),
                    (855usize, 236usize),
                    (858usize, 237usize),
                    (859usize, 238usize),
                    (862usize, 239usize),
                    (863usize, 240usize),
                    (864usize, 241usize),
                    (871usize, 242usize),
                    (872usize, 243usize),
                    (873usize, 244usize),
                    (874usize, 245usize),
                ];
                let mut regular_idx: usize = 0;
                let mut ep_idx: usize = 0;
                let mut merged_idx: usize = 0;
                while merged_idx < 1258usize {
                    if ep_idx < 246usize && EXTRA_POS[ep_idx].0 == merged_idx {
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
                    (1744830467u32, 869usize),
                    (268435454u32, 646usize),
                    (133099247u32, 601usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 647usize),
                    (1744830467u32, 601usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 650usize),
                    (133099247u32, 602usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 651usize),
                    (1744830467u32, 602usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 656usize),
                    (133099247u32, 603usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 657usize),
                    (1744830467u32, 603usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 662usize),
                    (133099247u32, 604usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 663usize),
                    (1744830467u32, 604usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 668usize),
                    (133099247u32, 605usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 669usize),
                    (1744830467u32, 605usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 674usize),
                    (133099247u32, 606usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 675usize),
                    (1744830467u32, 606usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 680usize),
                    (133099247u32, 607usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 681usize),
                    (1744830467u32, 607usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 686usize),
                    (133099247u32, 608usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 687usize),
                    (1744830467u32, 608usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 692usize),
                    (133099247u32, 609usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 693usize),
                    (1744830467u32, 609usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 698usize),
                    (133099247u32, 610usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 699usize),
                    (1744830467u32, 610usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 704usize),
                    (133099247u32, 611usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 705usize),
                    (1744830467u32, 611usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 710usize),
                    (133099247u32, 612usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 711usize),
                    (1744830467u32, 612usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 716usize),
                    (133099247u32, 613usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 717usize),
                    (1744830467u32, 613usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 722usize),
                    (133099247u32, 614usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 723usize),
                    (1744830467u32, 614usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 728usize),
                    (133099247u32, 615usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 729usize),
                    (1744830467u32, 615usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 734usize),
                    (133099247u32, 616usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 735usize),
                    (1744830467u32, 616usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 740usize),
                    (133099247u32, 617usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 741usize),
                    (1744830467u32, 617usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 746usize),
                    (133099247u32, 618usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 747usize),
                    (1744830467u32, 618usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 752usize),
                    (133099247u32, 619usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 753usize),
                    (1744830467u32, 619usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 758usize),
                    (133099247u32, 620usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 759usize),
                    (1744830467u32, 620usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 764usize),
                    (133099247u32, 621usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 765usize),
                    (1744830467u32, 621usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 770usize),
                    (133099247u32, 622usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 771usize),
                    (1744830467u32, 622usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 776usize),
                    (133099247u32, 623usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 777usize),
                    (1744830467u32, 623usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 782usize),
                    (133099247u32, 624usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 783usize),
                    (1744830467u32, 624usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 788usize),
                    (133099247u32, 625usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 789usize),
                    (1744830467u32, 625usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 794usize),
                    (133099247u32, 626usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 795usize),
                    (1744830467u32, 626usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 798usize),
                    (133099247u32, 627usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 799usize),
                    (1744830467u32, 627usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 802usize),
                    (133099247u32, 628usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 803usize),
                    (1744830467u32, 628usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 806usize),
                    (133099247u32, 629usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 807usize),
                    (1744830467u32, 629usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 810usize),
                    (133099247u32, 630usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 811usize),
                    (1744830467u32, 630usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 814usize),
                    (133099247u32, 631usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 815usize),
                    (1744830467u32, 631usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 818usize),
                    (133099247u32, 632usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 819usize),
                    (1744830467u32, 632usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 822usize),
                    (133099247u32, 633usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 823usize),
                    (1744830467u32, 633usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 826usize),
                    (133099247u32, 634usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 827usize),
                    (1744830467u32, 634usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 830usize),
                    (133099247u32, 635usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 831usize),
                    (1744830467u32, 635usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 834usize),
                    (133099247u32, 636usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 835usize),
                    (1744830467u32, 636usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 838usize),
                    (133099247u32, 637usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 839usize),
                    (1744830467u32, 637usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 842usize),
                    (133099247u32, 638usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 843usize),
                    (1744830467u32, 638usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 846usize),
                    (133099247u32, 639usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 847usize),
                    (1744830467u32, 639usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 850usize),
                    (133099247u32, 640usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 851usize),
                    (1744830467u32, 640usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 854usize),
                    (133099247u32, 641usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 855usize),
                    (1744830467u32, 641usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 858usize),
                    (133099247u32, 642usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 859usize),
                    (1744830467u32, 642usize),
                    (1744830467u32, 869usize),
                    (268435454u32, 862usize),
                    (133099247u32, 643usize),
                    (1744830467u32, 870usize),
                    (268435454u32, 863usize),
                    (1744830467u32, 643usize),
                ];
                let mut _sc = 0;
                while _sc < 86usize {
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
                    (268435454u32, 135usize),
                    (268435454u32, 133usize),
                    (268435454u32, 136usize),
                    (16777216u32, 59usize),
                    (1996488705u32, 135usize),
                    (16777216u32, 16usize),
                    (16777216u32, 32usize),
                    (16777216u32, 97usize),
                    (1744831011u32, 129usize),
                    (1476396101u32, 130usize),
                    (1996488705u32, 133usize),
                    (268435454u32, 137usize),
                    (268435454u32, 138usize),
                    (268435454u32, 134usize),
                    (268435454u32, 139usize),
                    (16777216u32, 60usize),
                    (1996488705u32, 138usize),
                    (16777216u32, 18usize),
                    (16777216u32, 34usize),
                    (16777216u32, 98usize),
                    (16777216u32, 129usize),
                    (33554432u32, 130usize),
                    (1744831011u32, 131usize),
                    (1476396101u32, 132usize),
                    (1996488705u32, 134usize),
                    (268435454u32, 140usize),
                    (268435454u32, 147usize),
                    (268435454u32, 143usize),
                    (268435454u32, 149usize),
                    (268435454u32, 148usize),
                    (268435454u32, 144usize),
                    (268435454u32, 150usize),
                    (1048576u32, 32usize),
                    (2012217345u32, 147usize),
                    (2004877313u32, 148usize),
                    (1048576u32, 47usize),
                    (1048576u32, 139usize),
                    (268435456u32, 140usize),
                    (1744830499u32, 141usize),
                    (2012217345u32, 143usize),
                    (2004877313u32, 144usize),
                    (268435454u32, 151usize),
                    (268435454u32, 152usize),
                    (268435454u32, 145usize),
                    (268435454u32, 154usize),
                    (268435454u32, 153usize),
                    (268435454u32, 146usize),
                    (268435454u32, 155usize),
                    (1048576u32, 34usize),
                    (2012217345u32, 152usize),
                    (2004877313u32, 153usize),
                    (1048576u32, 48usize),
                    (1048576u32, 136usize),
                    (268435456u32, 137usize),
                    (1048576u32, 141usize),
                    (1744830499u32, 142usize),
                    (2012217345u32, 145usize),
                    (2004877313u32, 146usize),
                    (268435454u32, 156usize),
                    (268435454u32, 139usize),
                    (268435454u32, 161usize),
                    (268435454u32, 163usize),
                    (268435454u32, 140usize),
                    (16777216u32, 16usize),
                    (16777216u32, 32usize),
                    (16777216u32, 97usize),
                    (16777216u32, 99usize),
                    (1744831011u32, 129usize),
                    (1476396101u32, 130usize),
                    (16777216u32, 151usize),
                    (268435456u32, 154usize),
                    (134217727u32, 155usize),
                    (1744831011u32, 157usize),
                    (1476396101u32, 158usize),
                    (1996488705u32, 161usize),
                    (268435454u32, 164usize),
                    (268435454u32, 136usize),
                    (268435454u32, 162usize),
                    (268435454u32, 165usize),
                    (268435454u32, 137usize),
                    (16777216u32, 18usize),
                    (16777216u32, 34usize),
                    (16777216u32, 98usize),
                    (16777216u32, 100usize),
                    (16777216u32, 129usize),
                    (33554432u32, 130usize),
                    (1744831011u32, 131usize),
                    (1476396101u32, 132usize),
                    (268435456u32, 149usize),
                    (134217727u32, 150usize),
                    (16777216u32, 156usize),
                    (16777216u32, 157usize),
                    (33554432u32, 158usize),
                    (1744831011u32, 159usize),
                    (1476396101u32, 160usize),
                    (1996488705u32, 162usize),
                    (268435454u32, 166usize),
                    (268435454u32, 151usize),
                    (268435422u32, 154usize),
                    (268435454u32, 169usize),
                    (268435454u32, 171usize),
                    (268435454u32, 155usize),
                    (33554432u32, 47usize),
                    (33554432u32, 139usize),
                    (536870908u32, 140usize),
                    (1476396101u32, 141usize),
                    (33554432u32, 164usize),
                    (536870908u32, 165usize),
                    (1476396101u32, 167usize),
                    (1979711489u32, 169usize),
                    (268435454u32, 172usize),
                    (268435422u32, 149usize),
                    (268435454u32, 156usize),
                    (268435454u32, 170usize),
                    (268435454u32, 173usize),
                    (268435454u32, 150usize),
                    (33554432u32, 48usize),
                    (33554432u32, 136usize),
                    (536870908u32, 137usize),
                    (33554432u32, 141usize),
                    (1476396101u32, 142usize),
                    (536870908u32, 163usize),
                    (33554432u32, 166usize),
                    (33554432u32, 167usize),
                    (1476396101u32, 168usize),
                    (1979711489u32, 170usize),
                    (268435454u32, 174usize),
                    (268435454u32, 181usize),
                    (268435454u32, 179usize),
                    (268435454u32, 182usize),
                    (16777216u32, 55usize),
                    (1996488705u32, 181usize),
                    (16777216u32, 20usize),
                    (16777216u32, 36usize),
                    (16777216u32, 101usize),
                    (1744831011u32, 175usize),
                    (1476396101u32, 176usize),
                    (1996488705u32, 179usize),
                    (268435454u32, 183usize),
                    (268435454u32, 184usize),
                    (268435454u32, 180usize),
                    (268435454u32, 185usize),
                    (16777216u32, 56usize),
                    (1996488705u32, 184usize),
                    (16777216u32, 22usize),
                    (16777216u32, 38usize),
                    (16777216u32, 102usize),
                    (16777216u32, 175usize),
                    (33554432u32, 176usize),
                    (1744831011u32, 177usize),
                    (1476396101u32, 178usize),
                    (1996488705u32, 180usize),
                    (268435454u32, 186usize),
                    (268435454u32, 193usize),
                    (268435454u32, 189usize),
                    (268435454u32, 195usize),
                    (268435454u32, 194usize),
                    (268435454u32, 190usize),
                    (268435454u32, 196usize),
                    (1048576u32, 36usize),
                    (2012217345u32, 193usize),
                    (2004877313u32, 194usize),
                    (1048576u32, 49usize),
                    (1048576u32, 185usize),
                    (268435456u32, 186usize),
                    (1744830499u32, 187usize),
                    (2012217345u32, 189usize),
                    (2004877313u32, 190usize),
                    (268435454u32, 197usize),
                    (268435454u32, 198usize),
                    (268435454u32, 191usize),
                    (268435454u32, 200usize),
                    (268435454u32, 199usize),
                    (268435454u32, 192usize),
                    (268435454u32, 201usize),
                    (1048576u32, 38usize),
                    (2012217345u32, 198usize),
                    (2004877313u32, 199usize),
                    (1048576u32, 50usize),
                    (1048576u32, 182usize),
                    (268435456u32, 183usize),
                    (1048576u32, 187usize),
                    (1744830499u32, 188usize),
                    (2012217345u32, 191usize),
                    (2004877313u32, 192usize),
                    (268435454u32, 202usize),
                    (268435454u32, 185usize),
                    (268435454u32, 207usize),
                    (268435454u32, 209usize),
                    (268435454u32, 186usize),
                    (16777216u32, 20usize),
                    (16777216u32, 36usize),
                    (16777216u32, 101usize),
                    (16777216u32, 103usize),
                    (1744831011u32, 175usize),
                    (1476396101u32, 176usize),
                    (16777216u32, 197usize),
                    (268435456u32, 200usize),
                    (134217727u32, 201usize),
                    (1744831011u32, 203usize),
                    (1476396101u32, 204usize),
                    (1996488705u32, 207usize),
                    (268435454u32, 210usize),
                    (268435454u32, 182usize),
                    (268435454u32, 208usize),
                    (268435454u32, 211usize),
                    (268435454u32, 183usize),
                    (16777216u32, 22usize),
                    (16777216u32, 38usize),
                    (16777216u32, 102usize),
                    (16777216u32, 104usize),
                    (16777216u32, 175usize),
                    (33554432u32, 176usize),
                    (1744831011u32, 177usize),
                    (1476396101u32, 178usize),
                    (268435456u32, 195usize),
                    (134217727u32, 196usize),
                    (16777216u32, 202usize),
                    (16777216u32, 203usize),
                    (33554432u32, 204usize),
                    (1744831011u32, 205usize),
                    (1476396101u32, 206usize),
                    (1996488705u32, 208usize),
                    (268435454u32, 212usize),
                    (268435454u32, 197usize),
                    (268435422u32, 200usize),
                    (268435454u32, 215usize),
                    (268435454u32, 217usize),
                    (268435454u32, 201usize),
                    (33554432u32, 49usize),
                    (33554432u32, 185usize),
                    (536870908u32, 186usize),
                    (1476396101u32, 187usize),
                    (33554432u32, 210usize),
                    (536870908u32, 211usize),
                    (1476396101u32, 213usize),
                    (1979711489u32, 215usize),
                    (268435454u32, 218usize),
                    (268435422u32, 195usize),
                    (268435454u32, 202usize),
                    (268435454u32, 216usize),
                    (268435454u32, 219usize),
                    (268435454u32, 196usize),
                    (33554432u32, 50usize),
                    (33554432u32, 182usize),
                    (536870908u32, 183usize),
                    (33554432u32, 187usize),
                    (1476396101u32, 188usize),
                    (536870908u32, 209usize),
                    (33554432u32, 212usize),
                    (33554432u32, 213usize),
                    (1476396101u32, 214usize),
                    (1979711489u32, 216usize),
                    (268435454u32, 220usize),
                    (268435454u32, 227usize),
                    (268435454u32, 225usize),
                    (268435454u32, 228usize),
                    (16777216u32, 61usize),
                    (1996488705u32, 227usize),
                    (16777216u32, 24usize),
                    (16777216u32, 40usize),
                    (16777216u32, 105usize),
                    (1744831011u32, 221usize),
                    (1476396101u32, 222usize),
                    (1996488705u32, 225usize),
                    (268435454u32, 229usize),
                    (268435454u32, 230usize),
                    (268435454u32, 226usize),
                    (268435454u32, 231usize),
                    (16777216u32, 62usize),
                    (1996488705u32, 230usize),
                    (16777216u32, 26usize),
                    (16777216u32, 42usize),
                    (16777216u32, 106usize),
                    (16777216u32, 221usize),
                    (33554432u32, 222usize),
                    (1744831011u32, 223usize),
                    (1476396101u32, 224usize),
                    (1996488705u32, 226usize),
                    (268435454u32, 232usize),
                    (268435454u32, 239usize),
                    (268435454u32, 235usize),
                    (268435454u32, 241usize),
                    (268435454u32, 240usize),
                    (268435454u32, 236usize),
                    (268435454u32, 242usize),
                    (1048576u32, 40usize),
                    (2012217345u32, 239usize),
                    (2004877313u32, 240usize),
                    (1048576u32, 51usize),
                    (1048576u32, 231usize),
                    (268435456u32, 232usize),
                    (1744830499u32, 233usize),
                    (2012217345u32, 235usize),
                    (2004877313u32, 236usize),
                    (268435454u32, 243usize),
                    (268435454u32, 244usize),
                    (268435454u32, 237usize),
                    (268435454u32, 246usize),
                    (268435454u32, 245usize),
                    (268435454u32, 238usize),
                    (268435454u32, 247usize),
                    (1048576u32, 42usize),
                    (2012217345u32, 244usize),
                    (2004877313u32, 245usize),
                    (1048576u32, 52usize),
                    (1048576u32, 228usize),
                    (268435456u32, 229usize),
                    (1048576u32, 233usize),
                    (1744830499u32, 234usize),
                    (2012217345u32, 237usize),
                    (2004877313u32, 238usize),
                    (268435454u32, 248usize),
                    (268435454u32, 231usize),
                    (268435454u32, 253usize),
                    (268435454u32, 255usize),
                    (268435454u32, 232usize),
                    (16777216u32, 24usize),
                    (16777216u32, 40usize),
                    (16777216u32, 105usize),
                    (16777216u32, 107usize),
                    (1744831011u32, 221usize),
                    (1476396101u32, 222usize),
                    (16777216u32, 243usize),
                    (268435456u32, 246usize),
                    (134217727u32, 247usize),
                    (1744831011u32, 249usize),
                    (1476396101u32, 250usize),
                    (1996488705u32, 253usize),
                    (268435454u32, 256usize),
                    (268435454u32, 228usize),
                    (268435454u32, 254usize),
                    (268435454u32, 257usize),
                    (268435454u32, 229usize),
                    (16777216u32, 26usize),
                    (16777216u32, 42usize),
                    (16777216u32, 106usize),
                    (16777216u32, 108usize),
                    (16777216u32, 221usize),
                    (33554432u32, 222usize),
                    (1744831011u32, 223usize),
                    (1476396101u32, 224usize),
                    (268435456u32, 241usize),
                    (134217727u32, 242usize),
                    (16777216u32, 248usize),
                    (16777216u32, 249usize),
                    (33554432u32, 250usize),
                    (1744831011u32, 251usize),
                    (1476396101u32, 252usize),
                    (1996488705u32, 254usize),
                    (268435454u32, 258usize),
                    (268435454u32, 243usize),
                    (268435422u32, 246usize),
                    (268435454u32, 261usize),
                    (268435454u32, 263usize),
                    (268435454u32, 247usize),
                    (33554432u32, 51usize),
                    (33554432u32, 231usize),
                    (536870908u32, 232usize),
                    (1476396101u32, 233usize),
                    (33554432u32, 256usize),
                    (536870908u32, 257usize),
                    (1476396101u32, 259usize),
                    (1979711489u32, 261usize),
                    (268435454u32, 264usize),
                    (268435422u32, 241usize),
                    (268435454u32, 248usize),
                    (268435454u32, 262usize),
                    (268435454u32, 265usize),
                    (268435454u32, 242usize),
                    (33554432u32, 52usize),
                    (33554432u32, 228usize),
                    (536870908u32, 229usize),
                    (33554432u32, 233usize),
                    (1476396101u32, 234usize),
                    (536870908u32, 255usize),
                    (33554432u32, 258usize),
                    (33554432u32, 259usize),
                    (1476396101u32, 260usize),
                    (1979711489u32, 262usize),
                    (268435454u32, 266usize),
                    (268435454u32, 273usize),
                    (268435454u32, 271usize),
                    (268435454u32, 274usize),
                    (16777216u32, 57usize),
                    (1996488705u32, 273usize),
                    (16777216u32, 28usize),
                    (16777216u32, 44usize),
                    (16777216u32, 109usize),
                    (1744831011u32, 267usize),
                    (1476396101u32, 268usize),
                    (1996488705u32, 271usize),
                    (268435454u32, 275usize),
                    (268435454u32, 276usize),
                    (268435454u32, 272usize),
                    (268435454u32, 277usize),
                    (16777216u32, 58usize),
                    (1996488705u32, 276usize),
                    (16777216u32, 30usize),
                    (16777216u32, 46usize),
                    (16777216u32, 110usize),
                    (16777216u32, 267usize),
                    (33554432u32, 268usize),
                    (1744831011u32, 269usize),
                    (1476396101u32, 270usize),
                    (1996488705u32, 272usize),
                    (268435454u32, 278usize),
                    (268435454u32, 285usize),
                    (268435454u32, 281usize),
                    (268435454u32, 287usize),
                    (268435454u32, 286usize),
                    (268435454u32, 282usize),
                    (268435454u32, 288usize),
                    (1048576u32, 44usize),
                    (2012217345u32, 285usize),
                    (2004877313u32, 286usize),
                    (1048576u32, 53usize),
                    (1048576u32, 277usize),
                    (268435456u32, 278usize),
                    (1744830499u32, 279usize),
                    (2012217345u32, 281usize),
                    (2004877313u32, 282usize),
                    (268435454u32, 289usize),
                    (268435454u32, 290usize),
                    (268435454u32, 283usize),
                    (268435454u32, 292usize),
                    (268435454u32, 291usize),
                    (268435454u32, 284usize),
                    (268435454u32, 293usize),
                    (1048576u32, 46usize),
                    (2012217345u32, 290usize),
                    (2004877313u32, 291usize),
                    (1048576u32, 54usize),
                    (1048576u32, 274usize),
                    (268435456u32, 275usize),
                    (1048576u32, 279usize),
                    (1744830499u32, 280usize),
                    (2012217345u32, 283usize),
                    (2004877313u32, 284usize),
                    (268435454u32, 294usize),
                    (268435454u32, 277usize),
                    (268435454u32, 299usize),
                    (268435454u32, 301usize),
                    (268435454u32, 278usize),
                    (16777216u32, 28usize),
                    (16777216u32, 44usize),
                    (16777216u32, 109usize),
                    (16777216u32, 111usize),
                    (1744831011u32, 267usize),
                    (1476396101u32, 268usize),
                    (16777216u32, 289usize),
                    (268435456u32, 292usize),
                    (134217727u32, 293usize),
                    (1744831011u32, 295usize),
                    (1476396101u32, 296usize),
                    (1996488705u32, 299usize),
                    (268435454u32, 302usize),
                    (268435454u32, 274usize),
                    (268435454u32, 300usize),
                    (268435454u32, 303usize),
                    (268435454u32, 275usize),
                    (16777216u32, 30usize),
                    (16777216u32, 46usize),
                    (16777216u32, 110usize),
                    (16777216u32, 112usize),
                    (16777216u32, 267usize),
                    (33554432u32, 268usize),
                    (1744831011u32, 269usize),
                    (1476396101u32, 270usize),
                    (268435456u32, 287usize),
                    (134217727u32, 288usize),
                    (16777216u32, 294usize),
                    (16777216u32, 295usize),
                    (33554432u32, 296usize),
                    (1744831011u32, 297usize),
                    (1476396101u32, 298usize),
                    (1996488705u32, 300usize),
                    (268435454u32, 304usize),
                    (268435454u32, 289usize),
                    (268435422u32, 292usize),
                    (268435454u32, 307usize),
                    (268435454u32, 309usize),
                    (268435454u32, 293usize),
                    (33554432u32, 53usize),
                    (33554432u32, 277usize),
                    (536870908u32, 278usize),
                    (1476396101u32, 279usize),
                    (33554432u32, 302usize),
                    (536870908u32, 303usize),
                    (1476396101u32, 305usize),
                    (1979711489u32, 307usize),
                    (268435454u32, 310usize),
                    (268435422u32, 287usize),
                    (268435454u32, 294usize),
                    (268435454u32, 308usize),
                    (268435454u32, 311usize),
                    (268435454u32, 288usize),
                    (33554432u32, 54usize),
                    (33554432u32, 274usize),
                    (536870908u32, 275usize),
                    (33554432u32, 279usize),
                    (1476396101u32, 280usize),
                    (536870908u32, 301usize),
                    (33554432u32, 304usize),
                    (33554432u32, 305usize),
                    (1476396101u32, 306usize),
                    (1979711489u32, 308usize),
                    (268435454u32, 312usize),
                    (268435454u32, 302usize),
                    (268435454u32, 317usize),
                    (268435454u32, 319usize),
                    (268435454u32, 303usize),
                    (16777216u32, 16usize),
                    (16777216u32, 32usize),
                    (16777216u32, 97usize),
                    (16777216u32, 99usize),
                    (16777216u32, 113usize),
                    (1744831011u32, 129usize),
                    (1476396101u32, 130usize),
                    (16777216u32, 151usize),
                    (268435456u32, 154usize),
                    (134217727u32, 155usize),
                    (1744831011u32, 157usize),
                    (1476396101u32, 158usize),
                    (16777216u32, 218usize),
                    (536870908u32, 219usize),
                    (1744831011u32, 313usize),
                    (1476396101u32, 314usize),
                    (1996488705u32, 317usize),
                    (268435454u32, 320usize),
                    (268435454u32, 304usize),
                    (268435454u32, 318usize),
                    (268435454u32, 321usize),
                    (268435454u32, 301usize),
                    (16777216u32, 18usize),
                    (16777216u32, 34usize),
                    (16777216u32, 98usize),
                    (16777216u32, 100usize),
                    (16777216u32, 114usize),
                    (16777216u32, 129usize),
                    (33554432u32, 130usize),
                    (1744831011u32, 131usize),
                    (1476396101u32, 132usize),
                    (268435456u32, 149usize),
                    (134217727u32, 150usize),
                    (16777216u32, 156usize),
                    (16777216u32, 157usize),
                    (33554432u32, 158usize),
                    (1744831011u32, 159usize),
                    (1476396101u32, 160usize),
                    (536870908u32, 217usize),
                    (16777216u32, 220usize),
                    (16777216u32, 313usize),
                    (33554432u32, 314usize),
                    (1744831011u32, 315usize),
                    (1476396101u32, 316usize),
                    (1996488705u32, 318usize),
                    (268435454u32, 322usize),
                    (268435454u32, 329usize),
                    (268435454u32, 325usize),
                    (268435454u32, 331usize),
                    (268435454u32, 330usize),
                    (268435454u32, 326usize),
                    (268435454u32, 332usize),
                    (1048576u32, 218usize),
                    (536870912u32, 219usize),
                    (2012217345u32, 329usize),
                    (2004877313u32, 330usize),
                    (1048576u32, 51usize),
                    (1048576u32, 231usize),
                    (268435456u32, 232usize),
                    (1744830499u32, 233usize),
                    (1048576u32, 256usize),
                    (268435456u32, 257usize),
                    (1744830499u32, 259usize),
                    (1048576u32, 321usize),
                    (268435456u32, 322usize),
                    (1744830499u32, 323usize),
                    (2012217345u32, 325usize),
                    (2004877313u32, 326usize),
                    (268435454u32, 333usize),
                    (268435454u32, 334usize),
                    (268435454u32, 327usize),
                    (268435454u32, 336usize),
                    (268435454u32, 335usize),
                    (268435454u32, 328usize),
                    (268435454u32, 337usize),
                    (536870912u32, 217usize),
                    (1048576u32, 220usize),
                    (2012217345u32, 334usize),
                    (2004877313u32, 335usize),
                    (1048576u32, 52usize),
                    (1048576u32, 228usize),
                    (268435456u32, 229usize),
                    (1048576u32, 233usize),
                    (1744830499u32, 234usize),
                    (268435456u32, 255usize),
                    (1048576u32, 258usize),
                    (1048576u32, 259usize),
                    (1744830499u32, 260usize),
                    (1048576u32, 319usize),
                    (268435456u32, 320usize),
                    (1048576u32, 323usize),
                    (1744830499u32, 324usize),
                    (2012217345u32, 327usize),
                    (2004877313u32, 328usize),
                    (268435454u32, 338usize),
                    (268435454u32, 321usize),
                    (268435454u32, 343usize),
                    (268435454u32, 345usize),
                    (268435454u32, 322usize),
                    (16777216u32, 16usize),
                    (16777216u32, 32usize),
                    (16777216u32, 97usize),
                    (16777216u32, 99usize),
                    (16777216u32, 113usize),
                    (16777216u32, 115usize),
                    (1744831011u32, 129usize),
                    (1476396101u32, 130usize),
                    (16777216u32, 151usize),
                    (268435456u32, 154usize),
                    (134217727u32, 155usize),
                    (1744831011u32, 157usize),
                    (1476396101u32, 158usize),
                    (16777216u32, 218usize),
                    (536870908u32, 219usize),
                    (1744831011u32, 313usize),
                    (1476396101u32, 314usize),
                    (16777216u32, 333usize),
                    (268435456u32, 336usize),
                    (134217727u32, 337usize),
                    (1744831011u32, 339usize),
                    (1476396101u32, 340usize),
                    (1996488705u32, 343usize),
                    (268435454u32, 346usize),
                    (268435454u32, 319usize),
                    (268435454u32, 344usize),
                    (268435454u32, 347usize),
                    (268435454u32, 320usize),
                    (16777216u32, 18usize),
                    (16777216u32, 34usize),
                    (16777216u32, 98usize),
                    (16777216u32, 100usize),
                    (16777216u32, 114usize),
                    (16777216u32, 116usize),
                    (16777216u32, 129usize),
                    (33554432u32, 130usize),
                    (1744831011u32, 131usize),
                    (1476396101u32, 132usize),
                    (268435456u32, 149usize),
                    (134217727u32, 150usize),
                    (16777216u32, 156usize),
                    (16777216u32, 157usize),
                    (33554432u32, 158usize),
                    (1744831011u32, 159usize),
                    (1476396101u32, 160usize),
                    (536870908u32, 217usize),
                    (16777216u32, 220usize),
                    (16777216u32, 313usize),
                    (33554432u32, 314usize),
                    (1744831011u32, 315usize),
                    (1476396101u32, 316usize),
                    (268435456u32, 331usize),
                    (134217727u32, 332usize),
                    (16777216u32, 338usize),
                    (16777216u32, 339usize),
                    (33554432u32, 340usize),
                    (1744831011u32, 341usize),
                    (1476396101u32, 342usize),
                    (1996488705u32, 344usize),
                    (268435454u32, 348usize),
                    (268435454u32, 333usize),
                    (268435422u32, 336usize),
                    (268435454u32, 351usize),
                    (268435454u32, 353usize),
                    (268435454u32, 337usize),
                    (33554432u32, 51usize),
                    (33554432u32, 231usize),
                    (536870908u32, 232usize),
                    (1476396101u32, 233usize),
                    (33554432u32, 256usize),
                    (536870908u32, 257usize),
                    (1476396101u32, 259usize),
                    (33554432u32, 321usize),
                    (536870908u32, 322usize),
                    (1476396101u32, 323usize),
                    (33554432u32, 346usize),
                    (536870908u32, 347usize),
                    (1476396101u32, 349usize),
                    (1979711489u32, 351usize),
                    (268435454u32, 354usize),
                    (268435422u32, 331usize),
                    (268435454u32, 338usize),
                    (268435454u32, 352usize),
                    (268435454u32, 355usize),
                    (268435454u32, 332usize),
                    (33554432u32, 52usize),
                    (33554432u32, 228usize),
                    (536870908u32, 229usize),
                    (33554432u32, 233usize),
                    (1476396101u32, 234usize),
                    (536870908u32, 255usize),
                    (33554432u32, 258usize),
                    (33554432u32, 259usize),
                    (1476396101u32, 260usize),
                    (33554432u32, 319usize),
                    (536870908u32, 320usize),
                    (33554432u32, 323usize),
                    (1476396101u32, 324usize),
                    (536870908u32, 345usize),
                    (33554432u32, 348usize),
                    (33554432u32, 349usize),
                    (1476396101u32, 350usize),
                    (1979711489u32, 352usize),
                    (268435454u32, 356usize),
                    (268435454u32, 164usize),
                    (268435454u32, 361usize),
                    (268435454u32, 363usize),
                    (268435454u32, 165usize),
                    (16777216u32, 20usize),
                    (16777216u32, 36usize),
                    (16777216u32, 101usize),
                    (16777216u32, 103usize),
                    (16777216u32, 117usize),
                    (1744831011u32, 175usize),
                    (1476396101u32, 176usize),
                    (16777216u32, 197usize),
                    (268435456u32, 200usize),
                    (134217727u32, 201usize),
                    (1744831011u32, 203usize),
                    (1476396101u32, 204usize),
                    (16777216u32, 264usize),
                    (536870908u32, 265usize),
                    (1744831011u32, 357usize),
                    (1476396101u32, 358usize),
                    (1996488705u32, 361usize),
                    (268435454u32, 364usize),
                    (268435454u32, 166usize),
                    (268435454u32, 362usize),
                    (268435454u32, 365usize),
                    (268435454u32, 163usize),
                    (16777216u32, 22usize),
                    (16777216u32, 38usize),
                    (16777216u32, 102usize),
                    (16777216u32, 104usize),
                    (16777216u32, 118usize),
                    (16777216u32, 175usize),
                    (33554432u32, 176usize),
                    (1744831011u32, 177usize),
                    (1476396101u32, 178usize),
                    (268435456u32, 195usize),
                    (134217727u32, 196usize),
                    (16777216u32, 202usize),
                    (16777216u32, 203usize),
                    (33554432u32, 204usize),
                    (1744831011u32, 205usize),
                    (1476396101u32, 206usize),
                    (536870908u32, 263usize),
                    (16777216u32, 266usize),
                    (16777216u32, 357usize),
                    (33554432u32, 358usize),
                    (1744831011u32, 359usize),
                    (1476396101u32, 360usize),
                    (1996488705u32, 362usize),
                    (268435454u32, 366usize),
                    (268435454u32, 373usize),
                    (268435454u32, 369usize),
                    (268435454u32, 375usize),
                    (268435454u32, 374usize),
                    (268435454u32, 370usize),
                    (268435454u32, 376usize),
                    (1048576u32, 264usize),
                    (536870912u32, 265usize),
                    (2012217345u32, 373usize),
                    (2004877313u32, 374usize),
                    (1048576u32, 53usize),
                    (1048576u32, 277usize),
                    (268435456u32, 278usize),
                    (1744830499u32, 279usize),
                    (1048576u32, 302usize),
                    (268435456u32, 303usize),
                    (1744830499u32, 305usize),
                    (1048576u32, 365usize),
                    (268435456u32, 366usize),
                    (1744830499u32, 367usize),
                    (2012217345u32, 369usize),
                    (2004877313u32, 370usize),
                    (268435454u32, 377usize),
                    (268435454u32, 378usize),
                    (268435454u32, 371usize),
                    (268435454u32, 380usize),
                    (268435454u32, 379usize),
                    (268435454u32, 372usize),
                    (268435454u32, 381usize),
                    (536870912u32, 263usize),
                    (1048576u32, 266usize),
                    (2012217345u32, 378usize),
                    (2004877313u32, 379usize),
                    (1048576u32, 54usize),
                    (1048576u32, 274usize),
                    (268435456u32, 275usize),
                    (1048576u32, 279usize),
                    (1744830499u32, 280usize),
                    (268435456u32, 301usize),
                    (1048576u32, 304usize),
                    (1048576u32, 305usize),
                    (1744830499u32, 306usize),
                    (1048576u32, 363usize),
                    (268435456u32, 364usize),
                    (1048576u32, 367usize),
                    (1744830499u32, 368usize),
                    (2012217345u32, 371usize),
                    (2004877313u32, 372usize),
                    (268435454u32, 382usize),
                    (268435454u32, 365usize),
                    (268435454u32, 387usize),
                    (268435454u32, 389usize),
                    (268435454u32, 366usize),
                    (16777216u32, 20usize),
                    (16777216u32, 36usize),
                    (16777216u32, 101usize),
                    (16777216u32, 103usize),
                    (16777216u32, 117usize),
                    (16777216u32, 119usize),
                    (1744831011u32, 175usize),
                    (1476396101u32, 176usize),
                    (16777216u32, 197usize),
                    (268435456u32, 200usize),
                    (134217727u32, 201usize),
                    (1744831011u32, 203usize),
                    (1476396101u32, 204usize),
                    (16777216u32, 264usize),
                    (536870908u32, 265usize),
                    (1744831011u32, 357usize),
                    (1476396101u32, 358usize),
                    (16777216u32, 377usize),
                    (268435456u32, 380usize),
                    (134217727u32, 381usize),
                    (1744831011u32, 383usize),
                    (1476396101u32, 384usize),
                    (1996488705u32, 387usize),
                    (268435454u32, 390usize),
                    (268435454u32, 363usize),
                    (268435454u32, 388usize),
                    (268435454u32, 391usize),
                    (268435454u32, 364usize),
                    (16777216u32, 22usize),
                    (16777216u32, 38usize),
                    (16777216u32, 102usize),
                    (16777216u32, 104usize),
                    (16777216u32, 118usize),
                    (16777216u32, 120usize),
                    (16777216u32, 175usize),
                    (33554432u32, 176usize),
                    (1744831011u32, 177usize),
                    (1476396101u32, 178usize),
                    (268435456u32, 195usize),
                    (134217727u32, 196usize),
                    (16777216u32, 202usize),
                    (16777216u32, 203usize),
                    (33554432u32, 204usize),
                    (1744831011u32, 205usize),
                    (1476396101u32, 206usize),
                    (536870908u32, 263usize),
                    (16777216u32, 266usize),
                    (16777216u32, 357usize),
                    (33554432u32, 358usize),
                    (1744831011u32, 359usize),
                    (1476396101u32, 360usize),
                    (268435456u32, 375usize),
                    (134217727u32, 376usize),
                    (16777216u32, 382usize),
                    (16777216u32, 383usize),
                    (33554432u32, 384usize),
                    (1744831011u32, 385usize),
                    (1476396101u32, 386usize),
                    (1996488705u32, 388usize),
                    (268435454u32, 392usize),
                    (268435454u32, 377usize),
                    (268435422u32, 380usize),
                    (268435454u32, 395usize),
                    (268435454u32, 397usize),
                    (268435454u32, 381usize),
                    (33554432u32, 53usize),
                    (33554432u32, 277usize),
                    (536870908u32, 278usize),
                    (1476396101u32, 279usize),
                    (33554432u32, 302usize),
                    (536870908u32, 303usize),
                    (1476396101u32, 305usize),
                    (33554432u32, 365usize),
                    (536870908u32, 366usize),
                    (1476396101u32, 367usize),
                    (33554432u32, 390usize),
                    (536870908u32, 391usize),
                    (1476396101u32, 393usize),
                    (1979711489u32, 395usize),
                    (268435454u32, 398usize),
                    (268435422u32, 375usize),
                    (268435454u32, 382usize),
                    (268435454u32, 396usize),
                    (268435454u32, 399usize),
                    (268435454u32, 376usize),
                    (33554432u32, 54usize),
                    (33554432u32, 274usize),
                    (536870908u32, 275usize),
                    (33554432u32, 279usize),
                    (1476396101u32, 280usize),
                    (536870908u32, 301usize),
                    (33554432u32, 304usize),
                    (33554432u32, 305usize),
                    (1476396101u32, 306usize),
                    (33554432u32, 363usize),
                    (536870908u32, 364usize),
                    (33554432u32, 367usize),
                    (1476396101u32, 368usize),
                    (536870908u32, 389usize),
                    (33554432u32, 392usize),
                    (33554432u32, 393usize),
                    (1476396101u32, 394usize),
                    (1979711489u32, 396usize),
                    (268435454u32, 400usize),
                    (268435454u32, 210usize),
                    (268435454u32, 405usize),
                    (268435454u32, 407usize),
                    (268435454u32, 211usize),
                    (16777216u32, 24usize),
                    (16777216u32, 40usize),
                    (16777216u32, 105usize),
                    (16777216u32, 107usize),
                    (16777216u32, 121usize),
                    (1744831011u32, 221usize),
                    (1476396101u32, 222usize),
                    (16777216u32, 243usize),
                    (268435456u32, 246usize),
                    (134217727u32, 247usize),
                    (1744831011u32, 249usize),
                    (1476396101u32, 250usize),
                    (16777216u32, 310usize),
                    (536870908u32, 311usize),
                    (1744831011u32, 401usize),
                    (1476396101u32, 402usize),
                    (1996488705u32, 405usize),
                    (268435454u32, 408usize),
                    (268435454u32, 212usize),
                    (268435454u32, 406usize),
                    (268435454u32, 409usize),
                    (268435454u32, 209usize),
                    (16777216u32, 26usize),
                    (16777216u32, 42usize),
                    (16777216u32, 106usize),
                    (16777216u32, 108usize),
                    (16777216u32, 122usize),
                    (16777216u32, 221usize),
                    (33554432u32, 222usize),
                    (1744831011u32, 223usize),
                    (1476396101u32, 224usize),
                    (268435456u32, 241usize),
                    (134217727u32, 242usize),
                    (16777216u32, 248usize),
                    (16777216u32, 249usize),
                    (33554432u32, 250usize),
                    (1744831011u32, 251usize),
                    (1476396101u32, 252usize),
                    (536870908u32, 309usize),
                    (16777216u32, 312usize),
                    (16777216u32, 401usize),
                    (33554432u32, 402usize),
                    (1744831011u32, 403usize),
                    (1476396101u32, 404usize),
                    (1996488705u32, 406usize),
                    (268435454u32, 410usize),
                    (268435454u32, 417usize),
                    (268435454u32, 413usize),
                    (268435454u32, 419usize),
                    (268435454u32, 418usize),
                    (268435454u32, 414usize),
                    (268435454u32, 420usize),
                    (1048576u32, 310usize),
                    (536870912u32, 311usize),
                    (2012217345u32, 417usize),
                    (2004877313u32, 418usize),
                    (1048576u32, 47usize),
                    (1048576u32, 139usize),
                    (268435456u32, 140usize),
                    (1744830499u32, 141usize),
                    (1048576u32, 164usize),
                    (268435456u32, 165usize),
                    (1744830499u32, 167usize),
                    (1048576u32, 409usize),
                    (268435456u32, 410usize),
                    (1744830499u32, 411usize),
                    (2012217345u32, 413usize),
                    (2004877313u32, 414usize),
                    (268435454u32, 421usize),
                    (268435454u32, 422usize),
                    (268435454u32, 415usize),
                    (268435454u32, 424usize),
                    (268435454u32, 423usize),
                    (268435454u32, 416usize),
                    (268435454u32, 425usize),
                    (536870912u32, 309usize),
                    (1048576u32, 312usize),
                    (2012217345u32, 422usize),
                    (2004877313u32, 423usize),
                    (1048576u32, 48usize),
                    (1048576u32, 136usize),
                    (268435456u32, 137usize),
                    (1048576u32, 141usize),
                    (1744830499u32, 142usize),
                    (268435456u32, 163usize),
                    (1048576u32, 166usize),
                    (1048576u32, 167usize),
                    (1744830499u32, 168usize),
                    (1048576u32, 407usize),
                    (268435456u32, 408usize),
                    (1048576u32, 411usize),
                    (1744830499u32, 412usize),
                    (2012217345u32, 415usize),
                    (2004877313u32, 416usize),
                    (268435454u32, 426usize),
                    (268435454u32, 409usize),
                    (268435454u32, 431usize),
                    (268435454u32, 433usize),
                    (268435454u32, 410usize),
                    (16777216u32, 24usize),
                    (16777216u32, 40usize),
                    (16777216u32, 105usize),
                    (16777216u32, 107usize),
                    (16777216u32, 121usize),
                    (16777216u32, 123usize),
                    (1744831011u32, 221usize),
                    (1476396101u32, 222usize),
                    (16777216u32, 243usize),
                    (268435456u32, 246usize),
                    (134217727u32, 247usize),
                    (1744831011u32, 249usize),
                    (1476396101u32, 250usize),
                    (16777216u32, 310usize),
                    (536870908u32, 311usize),
                    (1744831011u32, 401usize),
                    (1476396101u32, 402usize),
                    (16777216u32, 421usize),
                    (268435456u32, 424usize),
                    (134217727u32, 425usize),
                    (1744831011u32, 427usize),
                    (1476396101u32, 428usize),
                    (1996488705u32, 431usize),
                    (268435454u32, 434usize),
                    (268435454u32, 407usize),
                    (268435454u32, 432usize),
                    (268435454u32, 435usize),
                    (268435454u32, 408usize),
                    (16777216u32, 26usize),
                    (16777216u32, 42usize),
                    (16777216u32, 106usize),
                    (16777216u32, 108usize),
                    (16777216u32, 122usize),
                    (16777216u32, 124usize),
                    (16777216u32, 221usize),
                    (33554432u32, 222usize),
                    (1744831011u32, 223usize),
                    (1476396101u32, 224usize),
                    (268435456u32, 241usize),
                    (134217727u32, 242usize),
                    (16777216u32, 248usize),
                    (16777216u32, 249usize),
                    (33554432u32, 250usize),
                    (1744831011u32, 251usize),
                    (1476396101u32, 252usize),
                    (536870908u32, 309usize),
                    (16777216u32, 312usize),
                    (16777216u32, 401usize),
                    (33554432u32, 402usize),
                    (1744831011u32, 403usize),
                    (1476396101u32, 404usize),
                    (268435456u32, 419usize),
                    (134217727u32, 420usize),
                    (16777216u32, 426usize),
                    (16777216u32, 427usize),
                    (33554432u32, 428usize),
                    (1744831011u32, 429usize),
                    (1476396101u32, 430usize),
                    (1996488705u32, 432usize),
                    (268435454u32, 436usize),
                    (268435454u32, 421usize),
                    (268435422u32, 424usize),
                    (268435454u32, 439usize),
                    (268435454u32, 441usize),
                    (268435454u32, 425usize),
                    (33554432u32, 47usize),
                    (33554432u32, 139usize),
                    (536870908u32, 140usize),
                    (1476396101u32, 141usize),
                    (33554432u32, 164usize),
                    (536870908u32, 165usize),
                    (1476396101u32, 167usize),
                    (33554432u32, 409usize),
                    (536870908u32, 410usize),
                    (1476396101u32, 411usize),
                    (33554432u32, 434usize),
                    (536870908u32, 435usize),
                    (1476396101u32, 437usize),
                    (1979711489u32, 439usize),
                    (268435454u32, 442usize),
                    (268435422u32, 419usize),
                    (268435454u32, 426usize),
                    (268435454u32, 440usize),
                    (268435454u32, 443usize),
                    (268435454u32, 420usize),
                    (33554432u32, 48usize),
                    (33554432u32, 136usize),
                    (536870908u32, 137usize),
                    (33554432u32, 141usize),
                    (1476396101u32, 142usize),
                    (536870908u32, 163usize),
                    (33554432u32, 166usize),
                    (33554432u32, 167usize),
                    (1476396101u32, 168usize),
                    (33554432u32, 407usize),
                    (536870908u32, 408usize),
                    (33554432u32, 411usize),
                    (1476396101u32, 412usize),
                    (536870908u32, 433usize),
                    (33554432u32, 436usize),
                    (33554432u32, 437usize),
                    (1476396101u32, 438usize),
                    (1979711489u32, 440usize),
                    (268435454u32, 444usize),
                    (268435454u32, 256usize),
                    (268435454u32, 449usize),
                    (268435454u32, 451usize),
                    (268435454u32, 257usize),
                    (16777216u32, 28usize),
                    (16777216u32, 44usize),
                    (16777216u32, 109usize),
                    (16777216u32, 111usize),
                    (16777216u32, 125usize),
                    (16777216u32, 172usize),
                    (536870908u32, 173usize),
                    (1744831011u32, 267usize),
                    (1476396101u32, 268usize),
                    (16777216u32, 289usize),
                    (268435456u32, 292usize),
                    (134217727u32, 293usize),
                    (1744831011u32, 295usize),
                    (1476396101u32, 296usize),
                    (1744831011u32, 445usize),
                    (1476396101u32, 446usize),
                    (1996488705u32, 449usize),
                    (268435454u32, 452usize),
                    (268435454u32, 258usize),
                    (268435454u32, 450usize),
                    (268435454u32, 453usize),
                    (268435454u32, 255usize),
                    (16777216u32, 30usize),
                    (16777216u32, 46usize),
                    (16777216u32, 110usize),
                    (16777216u32, 112usize),
                    (16777216u32, 126usize),
                    (536870908u32, 171usize),
                    (16777216u32, 174usize),
                    (16777216u32, 267usize),
                    (33554432u32, 268usize),
                    (1744831011u32, 269usize),
                    (1476396101u32, 270usize),
                    (268435456u32, 287usize),
                    (134217727u32, 288usize),
                    (16777216u32, 294usize),
                    (16777216u32, 295usize),
                    (33554432u32, 296usize),
                    (1744831011u32, 297usize),
                    (1476396101u32, 298usize),
                    (16777216u32, 445usize),
                    (33554432u32, 446usize),
                    (1744831011u32, 447usize),
                    (1476396101u32, 448usize),
                    (1996488705u32, 450usize),
                    (268435454u32, 454usize),
                    (268435454u32, 461usize),
                    (268435454u32, 457usize),
                    (268435454u32, 463usize),
                    (268435454u32, 462usize),
                    (268435454u32, 458usize),
                    (268435454u32, 464usize),
                    (1048576u32, 172usize),
                    (536870912u32, 173usize),
                    (2012217345u32, 461usize),
                    (2004877313u32, 462usize),
                    (1048576u32, 49usize),
                    (1048576u32, 185usize),
                    (268435456u32, 186usize),
                    (1744830499u32, 187usize),
                    (1048576u32, 210usize),
                    (268435456u32, 211usize),
                    (1744830499u32, 213usize),
                    (1048576u32, 453usize),
                    (268435456u32, 454usize),
                    (1744830499u32, 455usize),
                    (2012217345u32, 457usize),
                    (2004877313u32, 458usize),
                    (268435454u32, 465usize),
                    (268435454u32, 466usize),
                    (268435454u32, 459usize),
                    (268435454u32, 468usize),
                    (268435454u32, 467usize),
                    (268435454u32, 460usize),
                    (268435454u32, 469usize),
                    (536870912u32, 171usize),
                    (1048576u32, 174usize),
                    (2012217345u32, 466usize),
                    (2004877313u32, 467usize),
                    (1048576u32, 50usize),
                    (1048576u32, 182usize),
                    (268435456u32, 183usize),
                    (1048576u32, 187usize),
                    (1744830499u32, 188usize),
                    (268435456u32, 209usize),
                    (1048576u32, 212usize),
                    (1048576u32, 213usize),
                    (1744830499u32, 214usize),
                    (1048576u32, 451usize),
                    (268435456u32, 452usize),
                    (1048576u32, 455usize),
                    (1744830499u32, 456usize),
                    (2012217345u32, 459usize),
                    (2004877313u32, 460usize),
                    (268435454u32, 470usize),
                    (268435454u32, 453usize),
                    (268435454u32, 475usize),
                    (268435454u32, 477usize),
                    (268435454u32, 454usize),
                    (16777216u32, 28usize),
                    (16777216u32, 44usize),
                    (16777216u32, 109usize),
                    (16777216u32, 111usize),
                    (16777216u32, 125usize),
                    (16777216u32, 127usize),
                    (16777216u32, 172usize),
                    (536870908u32, 173usize),
                    (1744831011u32, 267usize),
                    (1476396101u32, 268usize),
                    (16777216u32, 289usize),
                    (268435456u32, 292usize),
                    (134217727u32, 293usize),
                    (1744831011u32, 295usize),
                    (1476396101u32, 296usize),
                    (1744831011u32, 445usize),
                    (1476396101u32, 446usize),
                    (16777216u32, 465usize),
                    (268435456u32, 468usize),
                    (134217727u32, 469usize),
                    (1744831011u32, 471usize),
                    (1476396101u32, 472usize),
                    (1996488705u32, 475usize),
                    (268435454u32, 478usize),
                    (268435454u32, 451usize),
                    (268435454u32, 476usize),
                    (268435454u32, 479usize),
                    (268435454u32, 452usize),
                    (16777216u32, 30usize),
                    (16777216u32, 46usize),
                    (16777216u32, 110usize),
                    (16777216u32, 112usize),
                    (16777216u32, 126usize),
                    (16777216u32, 128usize),
                    (536870908u32, 171usize),
                    (16777216u32, 174usize),
                    (16777216u32, 267usize),
                    (33554432u32, 268usize),
                    (1744831011u32, 269usize),
                    (1476396101u32, 270usize),
                    (268435456u32, 287usize),
                    (134217727u32, 288usize),
                    (16777216u32, 294usize),
                    (16777216u32, 295usize),
                    (33554432u32, 296usize),
                    (1744831011u32, 297usize),
                    (1476396101u32, 298usize),
                    (16777216u32, 445usize),
                    (33554432u32, 446usize),
                    (1744831011u32, 447usize),
                    (1476396101u32, 448usize),
                    (268435456u32, 463usize),
                    (134217727u32, 464usize),
                    (16777216u32, 470usize),
                    (16777216u32, 471usize),
                    (33554432u32, 472usize),
                    (1744831011u32, 473usize),
                    (1476396101u32, 474usize),
                    (1996488705u32, 476usize),
                    (268435454u32, 480usize),
                    (268435454u32, 465usize),
                    (268435422u32, 468usize),
                    (268435454u32, 483usize),
                    (268435454u32, 485usize),
                    (268435454u32, 469usize),
                    (33554432u32, 49usize),
                    (33554432u32, 185usize),
                    (536870908u32, 186usize),
                    (1476396101u32, 187usize),
                    (33554432u32, 210usize),
                    (536870908u32, 211usize),
                    (1476396101u32, 213usize),
                    (33554432u32, 453usize),
                    (536870908u32, 454usize),
                    (1476396101u32, 455usize),
                    (33554432u32, 478usize),
                    (536870908u32, 479usize),
                    (1476396101u32, 481usize),
                    (1979711489u32, 483usize),
                    (268435454u32, 486usize),
                    (268435422u32, 463usize),
                    (268435454u32, 470usize),
                    (268435454u32, 484usize),
                    (268435454u32, 487usize),
                    (268435454u32, 464usize),
                    (33554432u32, 50usize),
                    (33554432u32, 182usize),
                    (536870908u32, 183usize),
                    (33554432u32, 187usize),
                    (1476396101u32, 188usize),
                    (536870908u32, 209usize),
                    (33554432u32, 212usize),
                    (33554432u32, 213usize),
                    (1476396101u32, 214usize),
                    (33554432u32, 451usize),
                    (536870908u32, 452usize),
                    (33554432u32, 455usize),
                    (1476396101u32, 456usize),
                    (536870908u32, 477usize),
                    (33554432u32, 480usize),
                    (33554432u32, 481usize),
                    (1476396101u32, 482usize),
                    (1979711489u32, 484usize),
                    (268435454u32, 488usize),
                    (268435454u32, 489usize),
                    (268435454u32, 439usize),
                    (268435454u32, 490usize),
                    (33554432u32, 15usize),
                    (1979711489u32, 489usize),
                    (33554432u32, 47usize),
                    (33554432u32, 139usize),
                    (536870908u32, 140usize),
                    (1476396101u32, 141usize),
                    (33554432u32, 164usize),
                    (536870908u32, 165usize),
                    (1476396101u32, 167usize),
                    (33554432u32, 409usize),
                    (536870908u32, 410usize),
                    (1476396101u32, 411usize),
                    (33554432u32, 434usize),
                    (536870908u32, 435usize),
                    (1476396101u32, 437usize),
                    (1979711489u32, 439usize),
                    (268435454u32, 491usize),
                    (268435454u32, 490usize),
                    (268435454u32, 492usize),
                    (268435454u32, 494usize),
                    (268435454u32, 491usize),
                    (33554432u32, 16usize),
                    (33554432u32, 32usize),
                    (33554432u32, 97usize),
                    (33554432u32, 99usize),
                    (33554432u32, 113usize),
                    (33554432u32, 115usize),
                    (1476396101u32, 129usize),
                    (939526281u32, 130usize),
                    (33554432u32, 151usize),
                    (536870912u32, 154usize),
                    (268435454u32, 155usize),
                    (1476396101u32, 157usize),
                    (939526281u32, 158usize),
                    (33554432u32, 218usize),
                    (1073741816u32, 219usize),
                    (1476396101u32, 313usize),
                    (939526281u32, 314usize),
                    (33554432u32, 333usize),
                    (536870912u32, 336usize),
                    (268435454u32, 337usize),
                    (1476396101u32, 339usize),
                    (939526281u32, 340usize),
                    (1979711489u32, 343usize),
                    (268435454u32, 493usize),
                    (268435454u32, 495usize),
                    (268435454u32, 496usize),
                    (268435454u32, 440usize),
                    (268435454u32, 497usize),
                    (33554432u32, 17usize),
                    (1979711489u32, 496usize),
                    (33554432u32, 48usize),
                    (33554432u32, 136usize),
                    (536870908u32, 137usize),
                    (33554432u32, 141usize),
                    (1476396101u32, 142usize),
                    (536870908u32, 163usize),
                    (33554432u32, 166usize),
                    (33554432u32, 167usize),
                    (1476396101u32, 168usize),
                    (33554432u32, 407usize),
                    (536870908u32, 408usize),
                    (33554432u32, 411usize),
                    (1476396101u32, 412usize),
                    (536870908u32, 433usize),
                    (33554432u32, 436usize),
                    (33554432u32, 437usize),
                    (1476396101u32, 438usize),
                    (1979711489u32, 440usize),
                    (268435454u32, 498usize),
                    (268435454u32, 497usize),
                    (268435454u32, 499usize),
                    (268435454u32, 501usize),
                    (268435454u32, 498usize),
                    (33554432u32, 18usize),
                    (33554432u32, 34usize),
                    (33554432u32, 98usize),
                    (33554432u32, 100usize),
                    (33554432u32, 114usize),
                    (33554432u32, 116usize),
                    (33554432u32, 129usize),
                    (67108864u32, 130usize),
                    (1476396101u32, 131usize),
                    (939526281u32, 132usize),
                    (536870912u32, 149usize),
                    (268435454u32, 150usize),
                    (33554432u32, 156usize),
                    (33554432u32, 157usize),
                    (67108864u32, 158usize),
                    (1476396101u32, 159usize),
                    (939526281u32, 160usize),
                    (1073741816u32, 217usize),
                    (33554432u32, 220usize),
                    (33554432u32, 313usize),
                    (67108864u32, 314usize),
                    (1476396101u32, 315usize),
                    (939526281u32, 316usize),
                    (536870912u32, 331usize),
                    (268435454u32, 332usize),
                    (33554432u32, 338usize),
                    (33554432u32, 339usize),
                    (67108864u32, 340usize),
                    (1476396101u32, 341usize),
                    (939526281u32, 342usize),
                    (1979711489u32, 344usize),
                    (268435454u32, 500usize),
                    (268435454u32, 502usize),
                    (268435454u32, 503usize),
                    (268435454u32, 483usize),
                    (268435454u32, 504usize),
                    (33554432u32, 19usize),
                    (1979711489u32, 503usize),
                    (33554432u32, 49usize),
                    (33554432u32, 185usize),
                    (536870908u32, 186usize),
                    (1476396101u32, 187usize),
                    (33554432u32, 210usize),
                    (536870908u32, 211usize),
                    (1476396101u32, 213usize),
                    (33554432u32, 453usize),
                    (536870908u32, 454usize),
                    (1476396101u32, 455usize),
                    (33554432u32, 478usize),
                    (536870908u32, 479usize),
                    (1476396101u32, 481usize),
                    (1979711489u32, 483usize),
                    (268435454u32, 505usize),
                    (268435454u32, 504usize),
                    (268435454u32, 506usize),
                    (268435454u32, 508usize),
                    (268435454u32, 505usize),
                    (33554432u32, 20usize),
                    (33554432u32, 36usize),
                    (33554432u32, 101usize),
                    (33554432u32, 103usize),
                    (33554432u32, 117usize),
                    (33554432u32, 119usize),
                    (1476396101u32, 175usize),
                    (939526281u32, 176usize),
                    (33554432u32, 197usize),
                    (536870912u32, 200usize),
                    (268435454u32, 201usize),
                    (1476396101u32, 203usize),
                    (939526281u32, 204usize),
                    (33554432u32, 264usize),
                    (1073741816u32, 265usize),
                    (1476396101u32, 357usize),
                    (939526281u32, 358usize),
                    (33554432u32, 377usize),
                    (536870912u32, 380usize),
                    (268435454u32, 381usize),
                    (1476396101u32, 383usize),
                    (939526281u32, 384usize),
                    (1979711489u32, 387usize),
                    (268435454u32, 507usize),
                    (268435454u32, 509usize),
                    (268435454u32, 510usize),
                    (268435454u32, 484usize),
                    (268435454u32, 511usize),
                    (33554432u32, 21usize),
                    (1979711489u32, 510usize),
                    (33554432u32, 50usize),
                    (33554432u32, 182usize),
                    (536870908u32, 183usize),
                    (33554432u32, 187usize),
                    (1476396101u32, 188usize),
                    (536870908u32, 209usize),
                    (33554432u32, 212usize),
                    (33554432u32, 213usize),
                    (1476396101u32, 214usize),
                    (33554432u32, 451usize),
                    (536870908u32, 452usize),
                    (33554432u32, 455usize),
                    (1476396101u32, 456usize),
                    (536870908u32, 477usize),
                    (33554432u32, 480usize),
                    (33554432u32, 481usize),
                    (1476396101u32, 482usize),
                    (1979711489u32, 484usize),
                    (268435454u32, 512usize),
                    (268435454u32, 511usize),
                    (268435454u32, 513usize),
                    (268435454u32, 515usize),
                    (268435454u32, 512usize),
                    (33554432u32, 22usize),
                    (33554432u32, 38usize),
                    (33554432u32, 102usize),
                    (33554432u32, 104usize),
                    (33554432u32, 118usize),
                    (33554432u32, 120usize),
                    (33554432u32, 175usize),
                    (67108864u32, 176usize),
                    (1476396101u32, 177usize),
                    (939526281u32, 178usize),
                    (536870912u32, 195usize),
                    (268435454u32, 196usize),
                    (33554432u32, 202usize),
                    (33554432u32, 203usize),
                    (67108864u32, 204usize),
                    (1476396101u32, 205usize),
                    (939526281u32, 206usize),
                    (1073741816u32, 263usize),
                    (33554432u32, 266usize),
                    (33554432u32, 357usize),
                    (67108864u32, 358usize),
                    (1476396101u32, 359usize),
                    (939526281u32, 360usize),
                    (536870912u32, 375usize),
                    (268435454u32, 376usize),
                    (33554432u32, 382usize),
                    (33554432u32, 383usize),
                    (67108864u32, 384usize),
                    (1476396101u32, 385usize),
                    (939526281u32, 386usize),
                    (1979711489u32, 388usize),
                    (268435454u32, 514usize),
                    (268435454u32, 516usize),
                    (268435454u32, 517usize),
                    (268435454u32, 351usize),
                    (268435454u32, 518usize),
                    (33554432u32, 23usize),
                    (1979711489u32, 517usize),
                    (33554432u32, 51usize),
                    (33554432u32, 231usize),
                    (536870908u32, 232usize),
                    (1476396101u32, 233usize),
                    (33554432u32, 256usize),
                    (536870908u32, 257usize),
                    (1476396101u32, 259usize),
                    (33554432u32, 321usize),
                    (536870908u32, 322usize),
                    (1476396101u32, 323usize),
                    (33554432u32, 346usize),
                    (536870908u32, 347usize),
                    (1476396101u32, 349usize),
                    (1979711489u32, 351usize),
                    (268435454u32, 519usize),
                    (268435454u32, 518usize),
                    (268435454u32, 520usize),
                    (268435454u32, 522usize),
                    (268435454u32, 519usize),
                    (33554432u32, 24usize),
                    (33554432u32, 40usize),
                    (33554432u32, 105usize),
                    (33554432u32, 107usize),
                    (33554432u32, 121usize),
                    (33554432u32, 123usize),
                    (1476396101u32, 221usize),
                    (939526281u32, 222usize),
                    (33554432u32, 243usize),
                    (536870912u32, 246usize),
                    (268435454u32, 247usize),
                    (1476396101u32, 249usize),
                    (939526281u32, 250usize),
                    (33554432u32, 310usize),
                    (1073741816u32, 311usize),
                    (1476396101u32, 401usize),
                    (939526281u32, 402usize),
                    (33554432u32, 421usize),
                    (536870912u32, 424usize),
                    (268435454u32, 425usize),
                    (1476396101u32, 427usize),
                    (939526281u32, 428usize),
                    (1979711489u32, 431usize),
                    (268435454u32, 521usize),
                    (268435454u32, 523usize),
                    (268435454u32, 524usize),
                    (268435454u32, 352usize),
                    (268435454u32, 525usize),
                    (33554432u32, 25usize),
                    (1979711489u32, 524usize),
                    (33554432u32, 52usize),
                    (33554432u32, 228usize),
                    (536870908u32, 229usize),
                    (33554432u32, 233usize),
                    (1476396101u32, 234usize),
                    (536870908u32, 255usize),
                    (33554432u32, 258usize),
                    (33554432u32, 259usize),
                    (1476396101u32, 260usize),
                    (33554432u32, 319usize),
                    (536870908u32, 320usize),
                    (33554432u32, 323usize),
                    (1476396101u32, 324usize),
                    (536870908u32, 345usize),
                    (33554432u32, 348usize),
                    (33554432u32, 349usize),
                    (1476396101u32, 350usize),
                    (1979711489u32, 352usize),
                    (268435454u32, 526usize),
                    (268435454u32, 525usize),
                    (268435454u32, 527usize),
                    (268435454u32, 529usize),
                    (268435454u32, 526usize),
                    (33554432u32, 26usize),
                    (33554432u32, 42usize),
                    (33554432u32, 106usize),
                    (33554432u32, 108usize),
                    (33554432u32, 122usize),
                    (33554432u32, 124usize),
                    (33554432u32, 221usize),
                    (67108864u32, 222usize),
                    (1476396101u32, 223usize),
                    (939526281u32, 224usize),
                    (536870912u32, 241usize),
                    (268435454u32, 242usize),
                    (33554432u32, 248usize),
                    (33554432u32, 249usize),
                    (67108864u32, 250usize),
                    (1476396101u32, 251usize),
                    (939526281u32, 252usize),
                    (1073741816u32, 309usize),
                    (33554432u32, 312usize),
                    (33554432u32, 401usize),
                    (67108864u32, 402usize),
                    (1476396101u32, 403usize),
                    (939526281u32, 404usize),
                    (536870912u32, 419usize),
                    (268435454u32, 420usize),
                    (33554432u32, 426usize),
                    (33554432u32, 427usize),
                    (67108864u32, 428usize),
                    (1476396101u32, 429usize),
                    (939526281u32, 430usize),
                    (1979711489u32, 432usize),
                    (268435454u32, 528usize),
                    (268435454u32, 530usize),
                    (268435454u32, 531usize),
                    (268435454u32, 395usize),
                    (268435454u32, 532usize),
                    (33554432u32, 27usize),
                    (1979711489u32, 531usize),
                    (33554432u32, 53usize),
                    (33554432u32, 277usize),
                    (536870908u32, 278usize),
                    (1476396101u32, 279usize),
                    (33554432u32, 302usize),
                    (536870908u32, 303usize),
                    (1476396101u32, 305usize),
                    (33554432u32, 365usize),
                    (536870908u32, 366usize),
                    (1476396101u32, 367usize),
                    (33554432u32, 390usize),
                    (536870908u32, 391usize),
                    (1476396101u32, 393usize),
                    (1979711489u32, 395usize),
                    (268435454u32, 533usize),
                    (268435454u32, 532usize),
                    (268435454u32, 534usize),
                    (268435454u32, 536usize),
                    (268435454u32, 533usize),
                    (33554432u32, 28usize),
                    (33554432u32, 44usize),
                    (33554432u32, 109usize),
                    (33554432u32, 111usize),
                    (33554432u32, 125usize),
                    (33554432u32, 127usize),
                    (33554432u32, 172usize),
                    (1073741816u32, 173usize),
                    (1476396101u32, 267usize),
                    (939526281u32, 268usize),
                    (33554432u32, 289usize),
                    (536870912u32, 292usize),
                    (268435454u32, 293usize),
                    (1476396101u32, 295usize),
                    (939526281u32, 296usize),
                    (1476396101u32, 445usize),
                    (939526281u32, 446usize),
                    (33554432u32, 465usize),
                    (536870912u32, 468usize),
                    (268435454u32, 469usize),
                    (1476396101u32, 471usize),
                    (939526281u32, 472usize),
                    (1979711489u32, 475usize),
                    (268435454u32, 535usize),
                    (268435454u32, 537usize),
                    (268435454u32, 538usize),
                    (268435454u32, 396usize),
                    (268435454u32, 539usize),
                    (33554432u32, 29usize),
                    (1979711489u32, 538usize),
                    (33554432u32, 54usize),
                    (33554432u32, 274usize),
                    (536870908u32, 275usize),
                    (33554432u32, 279usize),
                    (1476396101u32, 280usize),
                    (536870908u32, 301usize),
                    (33554432u32, 304usize),
                    (33554432u32, 305usize),
                    (1476396101u32, 306usize),
                    (33554432u32, 363usize),
                    (536870908u32, 364usize),
                    (33554432u32, 367usize),
                    (1476396101u32, 368usize),
                    (536870908u32, 389usize),
                    (33554432u32, 392usize),
                    (33554432u32, 393usize),
                    (1476396101u32, 394usize),
                    (1979711489u32, 396usize),
                    (268435454u32, 540usize),
                    (268435454u32, 539usize),
                    (268435454u32, 541usize),
                    (268435454u32, 543usize),
                    (268435454u32, 540usize),
                    (33554432u32, 30usize),
                    (33554432u32, 46usize),
                    (33554432u32, 110usize),
                    (33554432u32, 112usize),
                    (33554432u32, 126usize),
                    (33554432u32, 128usize),
                    (1073741816u32, 171usize),
                    (33554432u32, 174usize),
                    (33554432u32, 267usize),
                    (67108864u32, 268usize),
                    (1476396101u32, 269usize),
                    (939526281u32, 270usize),
                    (536870912u32, 287usize),
                    (268435454u32, 288usize),
                    (33554432u32, 294usize),
                    (33554432u32, 295usize),
                    (67108864u32, 296usize),
                    (1476396101u32, 297usize),
                    (939526281u32, 298usize),
                    (33554432u32, 445usize),
                    (67108864u32, 446usize),
                    (1476396101u32, 447usize),
                    (939526281u32, 448usize),
                    (536870912u32, 463usize),
                    (268435454u32, 464usize),
                    (33554432u32, 470usize),
                    (33554432u32, 471usize),
                    (67108864u32, 472usize),
                    (1476396101u32, 473usize),
                    (939526281u32, 474usize),
                    (1979711489u32, 476usize),
                    (268435454u32, 542usize),
                    (268435454u32, 544usize),
                    (268435454u32, 486usize),
                    (268435454u32, 545usize),
                    (268435454u32, 546usize),
                    (268435454u32, 487usize),
                    (8388608u32, 31usize),
                    (2004877313u32, 545usize),
                    (268435454u32, 547usize),
                    (268435454u32, 390usize),
                    (268435454u32, 548usize),
                    (268435454u32, 550usize),
                    (268435454u32, 391usize),
                    (536870908u32, 547usize),
                    (268435454u32, 549usize),
                    (268435454u32, 551usize),
                    (268435454u32, 488usize),
                    (268435454u32, 552usize),
                    (268435454u32, 553usize),
                    (268435454u32, 485usize),
                    (8388608u32, 33usize),
                    (2004877313u32, 552usize),
                    (268435454u32, 554usize),
                    (268435454u32, 392usize),
                    (268435454u32, 555usize),
                    (268435454u32, 557usize),
                    (268435454u32, 389usize),
                    (536870908u32, 554usize),
                    (268435454u32, 556usize),
                    (268435454u32, 558usize),
                    (268435454u32, 354usize),
                    (268435454u32, 559usize),
                    (268435454u32, 560usize),
                    (268435454u32, 355usize),
                    (8388608u32, 35usize),
                    (2004877313u32, 559usize),
                    (268435454u32, 561usize),
                    (268435454u32, 434usize),
                    (268435454u32, 562usize),
                    (268435454u32, 564usize),
                    (268435454u32, 435usize),
                    (536870908u32, 561usize),
                    (268435454u32, 563usize),
                    (268435454u32, 565usize),
                    (268435454u32, 356usize),
                    (268435454u32, 566usize),
                    (268435454u32, 567usize),
                    (268435454u32, 353usize),
                    (8388608u32, 37usize),
                    (2004877313u32, 566usize),
                    (268435454u32, 568usize),
                    (268435454u32, 436usize),
                    (268435454u32, 569usize),
                    (268435454u32, 571usize),
                    (268435454u32, 433usize),
                    (536870908u32, 568usize),
                    (268435454u32, 570usize),
                    (268435454u32, 572usize),
                    (268435454u32, 398usize),
                    (268435454u32, 573usize),
                    (268435454u32, 574usize),
                    (268435454u32, 399usize),
                    (8388608u32, 39usize),
                    (2004877313u32, 573usize),
                    (268435454u32, 575usize),
                    (268435454u32, 478usize),
                    (268435454u32, 576usize),
                    (268435454u32, 578usize),
                    (268435454u32, 479usize),
                    (536870908u32, 575usize),
                    (268435454u32, 577usize),
                    (268435454u32, 579usize),
                    (268435454u32, 400usize),
                    (268435454u32, 580usize),
                    (268435454u32, 581usize),
                    (268435454u32, 397usize),
                    (8388608u32, 41usize),
                    (2004877313u32, 580usize),
                    (268435454u32, 582usize),
                    (268435454u32, 480usize),
                    (268435454u32, 583usize),
                    (268435454u32, 585usize),
                    (268435454u32, 477usize),
                    (536870908u32, 582usize),
                    (268435454u32, 584usize),
                    (268435454u32, 586usize),
                    (268435454u32, 442usize),
                    (268435454u32, 587usize),
                    (268435454u32, 588usize),
                    (268435454u32, 443usize),
                    (8388608u32, 43usize),
                    (2004877313u32, 587usize),
                    (268435454u32, 589usize),
                    (268435454u32, 346usize),
                    (268435454u32, 590usize),
                    (268435454u32, 592usize),
                    (268435454u32, 347usize),
                    (536870908u32, 589usize),
                    (268435454u32, 591usize),
                    (268435454u32, 593usize),
                    (268435454u32, 444usize),
                    (268435454u32, 594usize),
                    (268435454u32, 595usize),
                    (268435454u32, 441usize),
                    (8388608u32, 45usize),
                    (2004877313u32, 594usize),
                    (268435454u32, 596usize),
                    (268435454u32, 348usize),
                    (268435454u32, 597usize),
                    (268435454u32, 599usize),
                ];
                let mut _vl = 0;
                while _vl < 207usize {
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
        draw_field_els_into::<DRAW_BUF_CAPACITY>(&mut hasher, &mut seed, draw_buf.as_mut_slice());
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
