use core::mem::MaybeUninit;
use verifier_common::blake2s_u32::{
    AlignedArray64, DelegatedBlake2sState, BLAKE2S_DIGEST_SIZE_U32_WORDS,
};
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::field::{Field, FieldExtension, PrimeField};
use verifier_common::field_ops;
use verifier_common::gkr::{GKRVerificationError, LazyVec};
use verifier_common::non_determinism_source::NonDeterminismSource;
use verifier_common::transcript::{Blake2sTranscript, Seed};
const EXT_DEGREE: usize = <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
const DRAW_BUF_CAPACITY: usize = 64;
#[inline(always)]
pub fn read_field_el<I: NonDeterminismSource>() -> BabyBearExt4 {
    let mut words = LazyVec::<BabyBearField, EXT_DEGREE>::new();
    for _ in 0..EXT_DEGREE {
        words.push(BabyBearField::from_reduced_raw_repr(I::read_word()));
    }
    unsafe { core::ptr::read(words.as_slice().as_ptr().cast::<BabyBearExt4>()) }
}
#[inline(always)]
pub fn read_field_els<I: NonDeterminismSource>(dst: &mut [BabyBearExt4]) {
    for el in dst.iter_mut() {
        *el = read_field_el::<I>();
    }
}
#[inline(always)]
pub fn commit_field_els(seed: &mut Seed, els: &[BabyBearExt4]) {
    let total = els.len() * EXT_DEGREE;
    let as_u32 = unsafe { core::slice::from_raw_parts(els.as_ptr().cast::<u32>(), total) };
    Blake2sTranscript::commit_with_seed(seed, as_u32);
}
#[inline(always)]
pub fn draw_field_els_into(
    hasher: &mut DelegatedBlake2sState,
    seed: &mut Seed,
    dst: &mut [BabyBearExt4],
) {
    let n = dst.len();
    let padded = (n * EXT_DEGREE).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);
    assert!(padded <= DRAW_BUF_CAPACITY, "draw buffer too small");
    let mut words = LazyVec::<u32, DRAW_BUF_CAPACITY>::new();
    unsafe {
        words.set_len(padded);
        Blake2sTranscript::draw_randomness_using_hasher(hasher, seed, words.as_mut_slice());
    }
    for (i, chunk) in words.as_slice()[..n * EXT_DEGREE]
        .chunks_exact(EXT_DEGREE)
        .enumerate()
    {
        let mut arr = LazyVec::<BabyBearField, EXT_DEGREE>::new();
        for &w in chunk {
            arr.push(BabyBearField::from_u32_with_reduction(w));
        }
        dst[i] = unsafe { core::ptr::read(arr.as_slice().as_ptr().cast::<BabyBearExt4>()) };
    }
}
#[inline(always)]
pub fn dot_eq<const N: usize>(values: &[BabyBearExt4; N], eq: &[BabyBearExt4; N]) -> BabyBearExt4 {
    let mut result = BabyBearExt4::ZERO;
    for i in 0..N {
        let mut t = unsafe { *values.get_unchecked(i) };
        field_ops::mul_assign(&mut t, &*unsafe { eq.get_unchecked(i) });
        field_ops::add_assign(&mut result, &t);
    }
    result
}
#[inline(always)]
pub fn make_eq_poly<const N: usize>(
    challenges: &[BabyBearExt4; N],
    buf: &mut LazyVec<BabyBearExt4, { 1 << N }>,
) {
    unsafe { buf.set_unchecked(0, BabyBearExt4::ONE) };
    let mut size = 1usize;
    let mut idx = N;
    for _ in 0..N {
        idx -= 1;
        let c = unsafe { *challenges.get_unchecked(idx) };
        let f1 = c;
        let mut f0 = BabyBearExt4::ONE;
        field_ops::sub_assign(&mut f0, &c);
        let half = size;
        for i in (0..half).rev() {
            let prev = unsafe { *buf.get_unchecked(i) };
            let mut left = prev;
            let mut right = prev;
            field_ops::mul_assign(&mut left, &f0);
            field_ops::mul_assign(&mut right, &f1);
            unsafe {
                buf.set_unchecked(i, left);
                buf.set_unchecked(i + half, right);
            }
        }
        size *= 2;
    }
    unsafe { buf.set_len(1 << N) };
}
#[inline(always)]
pub fn verify_sumcheck_rounds<
    I: NonDeterminismSource,
    const NUM_ROUNDS: usize,
    const COMMIT_BUF: usize,
>(
    seed: &mut Seed,
    initial_claim: BabyBearExt4,
    challenges: &mut [BabyBearExt4],
    layer_idx: usize,
) -> Result<(BabyBearExt4, BabyBearExt4), GKRVerificationError> {
    let mut claim = initial_claim;
    let mut eq_prefactor = BabyBearExt4::ONE;
    let coeff_data_words = 4 * EXT_DEGREE;
    let total_commit_words = BLAKE2S_DIGEST_SIZE_U32_WORDS + coeff_data_words;
    let mut commit_buf: AlignedArray64<u32, COMMIT_BUF> = AlignedArray64::from_value(0u32);
    let mut hasher = DelegatedBlake2sState::new();
    let mut draw_buf = [0u32; BLAKE2S_DIGEST_SIZE_U32_WORDS];
    for round in 0..NUM_ROUNDS {
        commit_buf[0..BLAKE2S_DIGEST_SIZE_U32_WORDS].copy_from_slice(&seed.0);
        for i in 0..coeff_data_words {
            commit_buf[BLAKE2S_DIGEST_SIZE_U32_WORDS + i] = I::read_word();
        }
        let coeffs = unsafe {
            &*commit_buf
                .as_ptr()
                .add(BLAKE2S_DIGEST_SIZE_U32_WORDS)
                .cast::<[BabyBearExt4; 4]>()
        };
        let p0 = coeffs[0];
        let mut p1 = coeffs[0];
        field_ops::add_assign(&mut p1, &coeffs[1]);
        field_ops::add_assign(&mut p1, &coeffs[2]);
        field_ops::add_assign(&mut p1, &coeffs[3]);
        let mut sum = p0;
        field_ops::add_assign(&mut sum, &p1);
        field_ops::mul_assign(&mut sum, &eq_prefactor);
        if sum != claim {
            return Err(GKRVerificationError::SumcheckRoundFailed {
                layer: layer_idx,
                round,
            });
        }
        Blake2sTranscript::commit_with_seed_using_hasher_and_aligned_buffer(
            &mut hasher,
            seed,
            &commit_buf,
            total_commit_words,
        );
        Blake2sTranscript::draw_randomness_using_hasher(&mut hasher, seed, &mut draw_buf);
        let r_k = {
            let mut arr = LazyVec::<BabyBearField, EXT_DEGREE>::new();
            for i in 0..EXT_DEGREE {
                let w = draw_buf[i];
                arr.push(BabyBearField::from_u32_with_reduction(w));
            }
            unsafe { core::ptr::read(arr.as_slice().as_ptr().cast::<BabyBearExt4>()) }
        };
        {
            let mut result = coeffs[3];
            field_ops::mul_assign(&mut result, &r_k);
            field_ops::add_assign(&mut result, &coeffs[2]);
            field_ops::mul_assign(&mut result, &r_k);
            field_ops::add_assign(&mut result, &coeffs[1]);
            field_ops::mul_assign(&mut result, &r_k);
            field_ops::add_assign(&mut result, &coeffs[0]);
            claim = result;
        }
        {
            let p = unsafe { *challenges.get_unchecked(round) };
            let mut one_minus_r = BabyBearExt4::ONE;
            field_ops::sub_assign(&mut one_minus_r, &r_k);
            let mut one_minus_p = BabyBearExt4::ONE;
            field_ops::sub_assign(&mut one_minus_p, &p);
            let mut t = one_minus_r;
            field_ops::mul_assign(&mut t, &one_minus_p);
            let mut rp = r_k;
            field_ops::mul_assign(&mut rp, &p);
            field_ops::add_assign(&mut t, &rp);
            eq_prefactor = t;
        }
        unsafe { *challenges.get_unchecked_mut(round) = r_k };
    }
    Ok((claim, eq_prefactor))
}
#[inline(always)]
pub fn verify_final_step_check(
    f: [BabyBearExt4; 2],
    last_prev_point: BabyBearExt4,
    final_eq_prefactor: BabyBearExt4,
    final_claim: BabyBearExt4,
    layer_idx: usize,
) -> Result<(), GKRVerificationError> {
    let mut eq0 = BabyBearExt4::ONE;
    field_ops::sub_assign(&mut eq0, &last_prev_point);
    let mut rhs = eq0;
    field_ops::mul_assign(&mut rhs, &f[0]);
    let mut t = last_prev_point;
    field_ops::mul_assign(&mut t, &f[1]);
    field_ops::add_assign(&mut rhs, &t);
    field_ops::mul_assign(&mut rhs, &final_eq_prefactor);
    if rhs != final_claim {
        return Err(GKRVerificationError::FinalStepCheckFailed { layer: layer_idx });
    }
    Ok(())
}
#[inline(always)]
pub fn fold_standard_claims<const NUM_ADDRS: usize, const ADDRS: usize, const BUF: usize>(
    eval_buf: &AlignedArray64<MaybeUninit<u32>, BUF>,
    last_r: BabyBearExt4,
    claims: &mut LazyVec<BabyBearExt4, ADDRS>,
) {
    let final_step_evals: &[[BabyBearExt4; 2]] =
        unsafe { eval_buf.transmute_subslice(BLAKE2S_DIGEST_SIZE_U32_WORDS, NUM_ADDRS) };
    claims.clear();
    for i in 0..NUM_ADDRS {
        let evals = unsafe { final_step_evals.get_unchecked(i) };
        let f0 = evals[0];
        let mut diff = evals[1];
        field_ops::sub_assign(&mut diff, &f0);
        field_ops::mul_assign(&mut diff, &last_r);
        field_ops::add_assign(&mut diff, &f0);
        claims.push(diff);
    }
}
#[derive(Clone, Debug)]
pub enum WhirVerificationError {
    SumcheckFailed { round: usize },
}
#[inline(always)]
pub fn verify_whir_sumcheck_step<I: NonDeterminismSource>(
    hasher: &mut DelegatedBlake2sState,
    seed: &mut Seed,
    claim: BabyBearExt4,
    round: usize,
) -> Result<(BabyBearExt4, BabyBearExt4), WhirVerificationError> {
    let c0 = read_field_el::<I>();
    let c1 = read_field_el::<I>();
    let c2 = read_field_el::<I>();
    let coeffs = [c0, c1, c2];
    commit_field_els(seed, &coeffs);
    let p0 = c0;
    let mut p1 = c0;
    field_ops::add_assign(&mut p1, &c1);
    field_ops::add_assign(&mut p1, &c2);
    let mut sum = p0;
    field_ops::add_assign(&mut sum, &p1);
    if sum != claim {
        return Err(WhirVerificationError::SumcheckFailed { round });
    }
    let mut challenge_buf = [BabyBearExt4::ZERO; 1];
    draw_field_els_into(hasher, seed, &mut challenge_buf);
    let alpha = challenge_buf[0];
    let mut new_claim = c2;
    field_ops::mul_assign(&mut new_claim, &alpha);
    field_ops::add_assign(&mut new_claim, &c1);
    field_ops::mul_assign(&mut new_claim, &alpha);
    field_ops::add_assign(&mut new_claim, &c0);
    Ok((new_claim, alpha))
}
#[inline(always)]
pub fn lagrange_eval_3pt(
    a: BabyBearExt4,
    b: BabyBearExt4,
    c: BabyBearExt4,
    alpha: BabyBearExt4,
) -> BabyBearExt4 {
    let mut p2 = a;
    field_ops::add_assign(&mut p2, &a);
    field_ops::add_assign(&mut p2, &b);
    field_ops::add_assign(&mut p2, &b);
    field_ops::sub_assign(&mut p2, &c);
    field_ops::sub_assign(&mut p2, &c);
    field_ops::sub_assign(&mut p2, &c);
    field_ops::sub_assign(&mut p2, &c);
    let mut p1 = b;
    field_ops::sub_assign(&mut p1, &a);
    field_ops::sub_assign(&mut p1, &p2);
    let mut inner = p2;
    field_ops::mul_assign(&mut inner, &alpha);
    field_ops::add_assign(&mut inner, &p1);
    field_ops::mul_assign(&mut inner, &alpha);
    field_ops::add_assign(&mut inner, &a);
    inner
}
#[inline(always)]
pub fn materialize_gamma_powers<const N: usize>(gamma: BabyBearExt4) -> [BabyBearExt4; N] {
    debug_assert!(N > 1);
    let mut powers: LazyVec<BabyBearExt4, N> = LazyVec::new();
    powers.push(BabyBearExt4::ONE);
    let mut i = 1;
    let mut gamma_pow = gamma;
    while i < N - 1 {
        powers.push(gamma_pow);
        field_ops::mul_assign(&mut gamma_pow, &gamma);
        i += 1;
    }
    powers.push(gamma_pow);
    unsafe { powers.into_array() }
}
#[inline(always)]
pub fn batch_claims<const NUM_CLAIMS: usize, const CAP: usize>(
    claims: &LazyVec<BabyBearExt4, CAP>,
    gamma_powers: &[BabyBearExt4; NUM_CLAIMS],
) -> BabyBearExt4 {
    debug_assert!(NUM_CLAIMS > 0);
    debug_assert!(NUM_CLAIMS <= CAP);
    let mut batched = *claims.get(0);
    let mut i = 1;
    while i < NUM_CLAIMS {
        let claim_i = *claims.get(i);
        let mut term = gamma_powers[i];
        field_ops::mul_assign(&mut term, &claim_i);
        field_ops::add_assign(&mut batched, &term);
        i += 1;
    }
    batched
}
#[inline(always)]
pub fn fold_coset(
    evals: &[BabyBearExt4],
    num_rounds: usize,
    folding_challenges: &[BabyBearExt4],
    mut root_inv: BabyBearField,
    high_powers_offsets: &[BabyBearField],
    two_inv: BabyBearField,
    buf_a: &mut [BabyBearExt4],
    buf_b: &mut [BabyBearExt4],
) -> BabyBearExt4 {
    debug_assert!(num_rounds == 0 || high_powers_offsets.len() >= 1 << (num_rounds - 1));
    let mut round = 0;
    while round < num_rounds {
        let half = 1 << (num_rounds - round - 1);
        let challenge = folding_challenges[round];
        let (src, dst) = if round == 0 {
            (evals, &mut buf_a[..half])
        } else if round % 2 == 1 {
            (&buf_a[..half * 2], &mut buf_b[..half])
        } else {
            (&buf_b[..half * 2], &mut buf_a[..half])
        };
        let mut pair_idx = 0;
        while pair_idx < half {
            let a = src[pair_idx * 2];
            let b = src[pair_idx * 2 + 1];
            let mut t = a;
            field_ops::sub_assign(&mut t, &b);
            field_ops::mul_assign(&mut t, &challenge);
            let mut root = root_inv;
            field_ops::mul_assign(&mut root, &high_powers_offsets[pair_idx]);
            field_ops::mul_assign_by_base(&mut t, &root);
            field_ops::add_assign(&mut t, &a);
            field_ops::add_assign(&mut t, &b);
            field_ops::mul_assign_by_base(&mut t, &two_inv);
            dst[pair_idx] = t;
            pair_idx += 1;
        }
        field_ops::square(&mut root_inv);
        round += 1;
    }
    if num_rounds == 0 {
        evals[0]
    } else if num_rounds % 2 == 1 {
        buf_a[0]
    } else {
        buf_b[0]
    }
}
