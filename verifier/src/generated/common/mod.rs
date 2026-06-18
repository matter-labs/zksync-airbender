use verifier_common::blake2s_u32::{DelegatedBlake2sState, BLAKE2S_DIGEST_SIZE_U32_WORDS};
use verifier_common::errors::ErrorCreator;
use verifier_common::field::baby_bear::base::BabyBearField;
use verifier_common::field::baby_bear::ext4::BabyBearExt4;
use verifier_common::field::{Field, FieldExtension, PrimeField};
use verifier_common::field_ops;
use verifier_common::lazy_vec::LazyVec;
use verifier_common::non_determinism_source::NonDeterminismSource;
pub use verifier_common::structs::{ext_from_nds, ext_from_raw_words};
use verifier_common::structs::{CommitBuf, TranscriptState};
pub use verifier_common::SUMCHECK_POLY_COEFFS;
pub const EXT_DEGREE: usize = <BabyBearExt4 as FieldExtension<BabyBearField>>::DEGREE;
#[inline(always)]
pub fn read_reduced_field_el<I: NonDeterminismSource>(nd_source: &mut I) -> u32 {
    nd_source.read_reduced_field_element(BabyBearField::ORDER)
}
#[inline(always)]
pub fn read_field_el<I: NonDeterminismSource>(nd_source: &mut I) -> BabyBearExt4 {
    ext_from_nds::<BabyBearField, BabyBearExt4, I>(nd_source)
}
#[inline(always)]
pub fn read_field_els<I: NonDeterminismSource>(dst: &mut [BabyBearExt4], nd_source: &mut I) {
    let mut i = 0;
    while i < dst.len() {
        dst[i] = read_field_el::<I>(nd_source);
        i += 1;
    }
}
#[inline(always)]
pub fn draw_field_els_into<const BUF_CAP: usize>(
    ts: &mut TranscriptState,
    dst: &mut [BabyBearExt4],
) {
    let n = dst.len();
    let padded = (n * EXT_DEGREE).next_multiple_of(BLAKE2S_DIGEST_SIZE_U32_WORDS);
    debug_assert!(padded <= BUF_CAP, "draw buffer too small");
    let mut words = LazyVec::<u32, BUF_CAP>::new();
    unsafe {
        words.set_len(padded);
        ts.draw_raw(words.as_mut_slice());
    }
    let mut i = 0;
    while i < n {
        let base = i * EXT_DEGREE;
        let raw = unsafe {
            (words.as_slice().as_ptr().add(base) as *const [u32; EXT_DEGREE]).as_ref_unchecked()
        };
        unsafe {
            *dst.get_unchecked_mut(i) =
                ext_from_raw_words::<BabyBearField, BabyBearExt4, EXT_DEGREE>(raw);
        }
        i += 1;
    }
}
#[inline(always)]
pub fn draw_single_field_el(ts: &mut TranscriptState) -> BabyBearExt4 {
    let mut words = LazyVec::<u32, BLAKE2S_DIGEST_SIZE_U32_WORDS>::new();
    unsafe {
        words.set_len(BLAKE2S_DIGEST_SIZE_U32_WORDS);
        ts.draw_raw(words.as_mut_slice());
    }
    let raw = unsafe { words.as_array::<EXT_DEGREE>() };
    ext_from_raw_words::<BabyBearField, BabyBearExt4, EXT_DEGREE>(raw)
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
pub fn make_eq_poly<const M: usize, const N: usize>(
    challenges: &[BabyBearExt4; M],
    buf: &mut LazyVec<BabyBearExt4, N>,
) {
    assert_eq!(N, 1 << M);
    unsafe { buf.set_unchecked(0, BabyBearExt4::ONE) };
    let mut size = 1usize;
    let mut idx = M;
    for _ in 0..M {
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
    unsafe { buf.set_len(N) };
}
#[inline(always)]
pub fn verify_sumcheck_rounds<
    I: NonDeterminismSource,
    E: ErrorCreator,
    const NUM_ROUNDS: usize,
    const COMMIT_BUF: usize,
>(
    ts: &mut TranscriptState,
    initial_claim: BabyBearExt4,
    challenges: &mut [BabyBearExt4],
    layer_idx: usize,
    nd_source: &mut I,
) -> Result<(BabyBearExt4, BabyBearExt4), E::Error> {
    let mut claim = initial_claim;
    let mut eq_prefactor = BabyBearExt4::ONE;
    let coeff_data_words = SUMCHECK_POLY_COEFFS * EXT_DEGREE;
    let mut commit_buf = CommitBuf::<COMMIT_BUF>::new();
    let mut draw_buf = LazyVec::<u32, BLAKE2S_DIGEST_SIZE_U32_WORDS>::new();
    unsafe {
        draw_buf.set_len(BLAKE2S_DIGEST_SIZE_U32_WORDS);
    }
    for round in 0..NUM_ROUNDS {
        {
            let mut i = 0;
            while i < coeff_data_words {
                commit_buf.data_write(i, read_reduced_field_el::<I>(nd_source));
                i += 1;
            }
        }
        let coeffs: [BabyBearExt4; 4] =
            unsafe { *commit_buf.data_as::<[BabyBearExt4; 4]>(1).as_ptr() };
        let p0 = coeffs[0];
        let mut p1 = coeffs[0];
        field_ops::add_assign(&mut p1, &coeffs[1]);
        field_ops::add_assign(&mut p1, &coeffs[2]);
        field_ops::add_assign(&mut p1, &coeffs[3]);
        let mut sum = p0;
        field_ops::add_assign(&mut sum, &p1);
        field_ops::mul_assign(&mut sum, &eq_prefactor);
        if sum != claim {
            return Err(E::gkr_sumcheck_round_failed(layer_idx, round));
        }
        ts.commit(&mut commit_buf, coeff_data_words);
        ts.draw_raw(draw_buf.as_mut_slice());
        let r_k = {
            let raw = unsafe {
                (draw_buf.as_slice().as_ptr() as *const [u32; EXT_DEGREE]).as_ref_unchecked()
            };
            ext_from_raw_words::<BabyBearField, BabyBearExt4, EXT_DEGREE>(raw)
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
pub fn verify_final_step_check<E: ErrorCreator>(
    f: [BabyBearExt4; 2],
    last_prev_point: BabyBearExt4,
    final_eq_prefactor: BabyBearExt4,
    final_claim: BabyBearExt4,
    layer_idx: usize,
) -> Result<(), E::Error> {
    let mut eq0 = BabyBearExt4::ONE;
    field_ops::sub_assign(&mut eq0, &last_prev_point);
    let mut rhs = eq0;
    field_ops::mul_assign(&mut rhs, &f[0]);
    let mut t = last_prev_point;
    field_ops::mul_assign(&mut t, &f[1]);
    field_ops::add_assign(&mut rhs, &t);
    field_ops::mul_assign(&mut rhs, &final_eq_prefactor);
    if rhs != final_claim {
        return Err(E::gkr_final_step_check_failed(layer_idx));
    }
    Ok(())
}
#[inline(always)]
pub fn fold_standard_claims<const NUM_ADDRS: usize, const ADDRS: usize, const BUF: usize>(
    eval_buf: &CommitBuf<BUF>,
    last_r: BabyBearExt4,
    claims: &mut LazyVec<BabyBearExt4, ADDRS>,
) {
    let final_step_evals: &[[BabyBearExt4; 2]] = unsafe { eval_buf.data_as(NUM_ADDRS) };
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
#[inline(always)]
#[allow(unused_variables)]
pub unsafe fn eval_linear_relation(
    evals: &[[BabyBearExt4; 2]],
    terms: &[(usize, usize)],
    constant: usize,
    j: usize,
) -> BabyBearExt4 {
    let mut result = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(constant as u32));
    let mut i = 0;
    while i < terms.len() {
        let (idx, coeff) = *terms.get_unchecked(i);
        let mut t = evals.get_unchecked(idx)[j];
        field_ops::mul_assign_by_base(&mut t, &BabyBearField::from_reduced_raw_repr(coeff as u32));
        field_ops::add_assign(&mut result, &t);
        i += 1;
    }
    result
}
#[inline(always)]
#[allow(unused_variables)]
pub unsafe fn eval_vector_lookup(
    evals: &[[BabyBearExt4; 2]],
    alpha: BabyBearExt4,
    col_descs: &[(usize, usize)],
    terms: &[(usize, usize)],
    j: usize,
) -> BabyBearExt4 {
    let mut result = BabyBearExt4::ZERO;
    let mut term_offset: usize = 0;
    let mut i = 0;
    while i < col_descs.len() {
        field_ops::mul_assign(&mut result, &alpha);
        let (col_const, num_terms) = *col_descs.get_unchecked(i);
        let mut col_val =
            BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(col_const as u32));
        let mut k = 0;
        while k < num_terms {
            let (idx, coeff) = *terms.get_unchecked(term_offset + k);
            let mut t = evals.get_unchecked(idx)[j];
            field_ops::mul_assign_by_base(
                &mut t,
                &BabyBearField::from_reduced_raw_repr(coeff as u32),
            );
            field_ops::add_assign(&mut col_val, &t);
            k += 1;
        }
        field_ops::add_assign(&mut result, &col_val);
        term_offset += num_terms;
        i += 1;
    }
    result
}
#[inline(always)]
#[allow(unused_variables)]
pub unsafe fn eval_max_quadratic(
    evals: &[[BabyBearExt4; 2]],
    quad_outer: &[(usize, usize)],
    quad_inner: &[(usize, usize)],
    linear: &[(usize, usize)],
    constant: usize,
    j: usize,
) -> BabyBearExt4 {
    let mut val = BabyBearExt4::from_base(BabyBearField::from_reduced_raw_repr(constant as u32));
    let mut inner_offset: usize = 0;
    let mut i = 0;
    while i < quad_outer.len() {
        let (addr_a, num_inner) = *quad_outer.get_unchecked(i);
        let mut inner = BabyBearExt4::ZERO;
        let mut k = 0;
        while k < num_inner {
            let (addr_b, coeff) = *quad_inner.get_unchecked(inner_offset + k);
            let mut t = evals.get_unchecked(addr_b)[j];
            field_ops::mul_assign_by_base(
                &mut t,
                &BabyBearField::from_reduced_raw_repr(coeff as u32),
            );
            field_ops::add_assign(&mut inner, &t);
            k += 1;
        }
        let a_val = evals.get_unchecked(addr_a)[j];
        field_ops::mul_assign(&mut inner, &a_val);
        field_ops::add_assign(&mut val, &inner);
        inner_offset += num_inner;
        i += 1;
    }
    let mut li = 0;
    while li < linear.len() {
        let (addr, coeff) = *linear.get_unchecked(li);
        let mut lt = evals.get_unchecked(addr)[j];
        field_ops::mul_assign_by_base(&mut lt, &BabyBearField::from_reduced_raw_repr(coeff as u32));
        field_ops::add_assign(&mut val, &lt);
        li += 1;
    }
    val
}
pub const ME_OP_ADD_BASE_CONST: usize = 0;
pub const ME_OP_ADD_EVAL: usize = 1;
pub const ME_OP_ADD_ONE_MINUS_EVAL: usize = 2;
pub const ME_OP_CH_MUL_EVAL: usize = 3;
pub const ME_OP_CH_MUL_CONST: usize = 4;
pub const ME_OP_CH_MUL_EVAL_PLUS_CONST: usize = 5;
pub const ME_OP_CH_MUL_EVAL_PLUS_DYN: usize = 6;
pub const ME_OP_BYTE_VALUE_PAIR: usize = 7;
#[inline(always)]
#[allow(unused_variables)]
pub unsafe fn eval_memory_expr(
    evals: &[[BabyBearExt4; 2]],
    challenges: &[BabyBearExt4],
    additive_part: BabyBearExt4,
    ops: &[[usize; 6]],
    j: usize,
) -> BabyBearExt4 {
    let mut result = additive_part;
    let mut i = 0;
    while i < ops.len() {
        let op = *ops.get_unchecked(i);
        match op[0] {
            ME_OP_ADD_BASE_CONST => {
                field_ops::add_assign_base(
                    &mut result,
                    &BabyBearField::from_reduced_raw_repr(op[1] as u32),
                );
            }
            ME_OP_ADD_EVAL => {
                field_ops::add_assign(&mut result, &evals.get_unchecked(op[1])[j]);
            }
            ME_OP_ADD_ONE_MINUS_EVAL => {
                let mut t = BabyBearExt4::ONE;
                field_ops::sub_assign(&mut t, &evals.get_unchecked(op[1])[j]);
                field_ops::add_assign(&mut result, &t);
            }
            ME_OP_CH_MUL_EVAL => {
                let mut t = challenges[op[1]];
                field_ops::mul_assign_by_base(&mut t, &evals.get_unchecked(op[2])[j]);
                field_ops::add_assign(&mut result, &t);
            }
            ME_OP_CH_MUL_CONST => {
                let mut t = challenges[op[1]];
                field_ops::mul_assign_by_base(
                    &mut t,
                    &BabyBearField::from_reduced_raw_repr(op[2] as u32),
                );
                field_ops::add_assign(&mut result, &t);
            }
            ME_OP_CH_MUL_EVAL_PLUS_CONST => {
                let mut ev = evals.get_unchecked(op[2])[j];
                field_ops::add_assign_base(
                    &mut ev,
                    &BabyBearField::from_reduced_raw_repr(op[3] as u32),
                );
                let mut t = challenges[op[1]];
                field_ops::mul_assign_by_base(&mut t, &ev);
                field_ops::add_assign(&mut result, &t);
            }
            ME_OP_CH_MUL_EVAL_PLUS_DYN => {
                let mut ev = evals.get_unchecked(op[2])[j];
                if op[4] != 0 {
                    field_ops::add_assign_base(
                        &mut ev,
                        &BabyBearField::from_reduced_raw_repr(op[4] as u32),
                    );
                }
                let mut dyn_val = evals.get_unchecked(op[3])[j];
                field_ops::mul_assign_by_base(
                    &mut dyn_val,
                    &BabyBearField::from_reduced_raw_repr(op[5] as u32),
                );
                field_ops::add_assign(&mut ev, &dyn_val);
                let mut t = challenges[op[1]];
                field_ops::mul_assign_by_base(&mut t, &ev);
                field_ops::add_assign(&mut result, &t);
            }
            ME_OP_BYTE_VALUE_PAIR => {
                let mut hi = evals.get_unchecked(op[3])[j];
                field_ops::mul_assign_by_base(
                    &mut hi,
                    &BabyBearField::from_u32_with_reduction(1u32 << 8),
                );
                field_ops::add_assign(&mut hi, &evals.get_unchecked(op[2])[j]);
                let mut t = challenges[op[1]];
                field_ops::mul_assign(&mut t, &hi);
                field_ops::add_assign(&mut result, &t);
            }
            _ => core::hint::unreachable_unchecked(),
        }
        i += 1;
    }
    result
}
#[inline(always)]
#[allow(unused_variables)]
pub unsafe fn compute_claim<const N: usize>(
    output_claims: &[BabyBearExt4],
    descs: &[(usize, usize, usize); N],
    batch_base: BabyBearExt4,
) -> BabyBearExt4 {
    let mut combined = BabyBearExt4::ZERO;
    let mut current_batch = BabyBearExt4::ONE;
    let mut i = 0;
    while i < N {
        let (n, o0, o1) = unsafe { *descs.get_unchecked(i) };
        if n == 0 {
            field_ops::mul_assign(&mut current_batch, &batch_base);
        } else if n == 1 {
            let claim = *output_claims.get_unchecked(o0);
            let mut t = current_batch;
            field_ops::mul_assign(&mut t, &claim);
            field_ops::add_assign(&mut combined, &t);
            field_ops::mul_assign(&mut current_batch, &batch_base);
        } else {
            let c0 = *output_claims.get_unchecked(o0);
            let mut t0 = current_batch;
            field_ops::mul_assign(&mut t0, &c0);
            field_ops::add_assign(&mut combined, &t0);
            field_ops::mul_assign(&mut current_batch, &batch_base);
            let c1 = *output_claims.get_unchecked(o1);
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
pub fn compute_tree_index(
    query_index: usize,
    num_cosets: usize,
    num_cosets_log2: usize,
    coset_tree_size: usize,
) -> usize {
    let coset_index = query_index & (num_cosets - 1);
    let internal_index = query_index >> num_cosets_log2;
    if num_cosets == 1 {
        internal_index
    } else {
        let coset_dest = coset_index.reverse_bits() >> (usize::BITS as usize - num_cosets_log2);
        coset_dest * coset_tree_size + internal_index
    }
}
#[inline(always)]
pub fn verify_whir_sumcheck_step<I: NonDeterminismSource, E: ErrorCreator>(
    ts: &mut TranscriptState,
    claim: BabyBearExt4,
    round: usize,
    nd_source: &mut I,
) -> Result<(BabyBearExt4, BabyBearExt4), E::Error> {
    const WHIR_SC_DATA_WORDS: usize = 3 * EXT_DEGREE;
    const WHIR_SC_COMMIT_BUF: usize = {
        let total = BLAKE2S_DIGEST_SIZE_U32_WORDS + WHIR_SC_DATA_WORDS;
        (total + ::verifier_common::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS - 1)
            / ::verifier_common::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS
            * ::verifier_common::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS
    };
    let mut buf = CommitBuf::<WHIR_SC_COMMIT_BUF>::new();
    {
        let mut i = 0;
        while i < WHIR_SC_DATA_WORDS {
            buf.data_write(i, read_reduced_field_el::<I>(nd_source));
            i += 1;
        }
    }
    let coeffs: [BabyBearExt4; 3] = unsafe { *buf.data_as::<[BabyBearExt4; 3]>(1).as_ptr() };
    let (c0, c1, c2) = (coeffs[0], coeffs[1], coeffs[2]);
    let p0 = c0;
    let mut p1 = c0;
    field_ops::add_assign(&mut p1, &c1);
    field_ops::add_assign(&mut p1, &c2);
    let mut sum = p0;
    field_ops::add_assign(&mut sum, &p1);
    if sum != claim {
        return Err(E::whir_sumcheck_failed(round));
    }
    ts.commit(&mut buf, WHIR_SC_DATA_WORDS);
    let alpha = draw_single_field_el(ts);
    let mut new_claim = c2;
    field_ops::mul_assign(&mut new_claim, &alpha);
    field_ops::add_assign(&mut new_claim, &c1);
    field_ops::mul_assign(&mut new_claim, &alpha);
    field_ops::add_assign(&mut new_claim, &c0);
    Ok((new_claim, alpha))
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
pub fn precompute_monomial_tensor<const N: usize>(
    challenges: &[BabyBearExt4],
    weights: &mut LazyVec<BabyBearExt4, N>,
) {
    let k = challenges.len();
    let len = 1usize << k;
    debug_assert!(len <= N);
    unsafe {
        weights.set_unchecked(0, BabyBearExt4::ONE);
    }
    let mut j = 0;
    while j < k {
        let alpha = unsafe { *challenges.get_unchecked(j) };
        let bit = 1usize << j;
        let mut i = bit;
        while i > 0 {
            i -= 1;
            let w = unsafe { *weights.get_unchecked(i) };
            let mut w_alpha = w;
            field_ops::mul_assign(&mut w_alpha, &alpha);
            unsafe {
                weights.set_unchecked(i + bit, w_alpha);
            }
        }
        j += 1;
    }
    unsafe {
        weights.set_len(len);
    }
}
#[inline(always)]
pub fn eval_multilinear_with_monomial_tensor(
    coeffs: &[BabyBearExt4],
    weights: &[BabyBearExt4],
) -> BabyBearExt4 {
    debug_assert_eq!(coeffs.len(), weights.len());
    debug_assert!(unsafe { *weights.get_unchecked(0) } == BabyBearExt4::ONE);
    let n = coeffs.len();
    let mut result = unsafe { *coeffs.get_unchecked(0) };
    let mut i = 1;
    while i < n {
        let mut term = unsafe { *coeffs.get_unchecked(i) };
        let w = unsafe { *weights.get_unchecked(i) };
        field_ops::mul_assign(&mut term, &w);
        field_ops::add_assign(&mut result, &term);
        i += 1;
    }
    result
}
pub const MAX_HIGH_POWERS: usize = 16usize;
#[inline(always)]
pub fn bitreverse_inplace<T: Copy>(arr: &mut [T]) {
    let n = arr.len();
    if n <= 1 {
        return;
    }
    let log_n = n.trailing_zeros();
    let mut i = 0;
    while i < n {
        let j = (i as u32).reverse_bits().wrapping_shr(32 - log_n) as usize;
        if i < j {
            unsafe {
                let tmp = *arr.get_unchecked(i);
                *arr.get_unchecked_mut(i) = *arr.get_unchecked(j);
                *arr.get_unchecked_mut(j) = tmp;
            }
        }
        i += 1;
    }
}
#[doc = r" Compute bit-reversed high powers of the set-generator inverse for fold_coset."]
#[inline(always)]
pub fn compute_high_powers_offsets(
    fold_steps: usize,
    dst: &mut LazyVec<BabyBearField, MAX_HIGH_POWERS>,
) {
    let count = 1usize << (fold_steps - 1);
    dst.push(BabyBearField::ONE);
    let set_gen_inv = BabyBearField::TWO_ADICITY_GENERATORS_INVERSED[fold_steps];
    let mut pow = set_gen_inv;
    let mut i = 1;
    while i < count {
        dst.push(pow);
        field_ops::mul_assign(&mut pow, &set_gen_inv);
        i += 1;
    }
    bitreverse_inplace(&mut dst.as_mut_slice()[..count]);
}
#[inline(always)]
pub fn ext_from_raw_word_slice(words: &[u32]) -> BabyBearExt4 {
    debug_assert!(words.len() >= EXT_DEGREE);
    let raw = unsafe { (words.as_ptr() as *const [u32; EXT_DEGREE]).as_ref_unchecked() };
    ext_from_raw_words::<BabyBearField, BabyBearExt4, EXT_DEGREE>(raw)
}
#[inline(always)]
#[allow(clippy::too_many_arguments)]
pub unsafe fn read_and_batch_leaf<I: NonDeterminismSource>(
    hash_buf: &mut [u32],
    num_columns: usize,
    gamma_powers: &[BabyBearExt4],
    gamma_offset: usize,
    acc0: &mut BabyBearExt4,
    acc1: &mut BabyBearExt4,
    nd_source: &mut I,
) {
    let mut col = 0;
    while col < num_columns {
        let gamma = *gamma_powers.get_unchecked(gamma_offset + col);
        let idx = col * 2;
        let raw = read_reduced_field_el::<I>(nd_source);
        *hash_buf.get_unchecked_mut(idx) = raw;
        let base_val = BabyBearField::from_reduced_raw_repr(raw);
        field_ops::add_assign_product_with_base(&mut *acc0, &gamma, &base_val);
        let raw = read_reduced_field_el::<I>(nd_source);
        *hash_buf.get_unchecked_mut(idx + 1) = raw;
        let base_val = BabyBearField::from_reduced_raw_repr(raw);
        field_ops::add_assign_product_with_base(&mut *acc1, &gamma, &base_val);
        col += 1;
    }
}
#[inline(always)]
pub fn fold_whir_accumulator<const MAX_POW: usize>(
    acc: &mut ::verifier_common::whir::WhirAccumulator<BabyBearExt4, MAX_POW>,
    alpha: BabyBearExt4,
    z_initial: &[BabyBearExt4],
) {
    let mut one_minus_alpha = BabyBearExt4::ONE;
    field_ops::sub_assign(&mut one_minus_alpha, &alpha);
    let mut two_alpha = alpha;
    field_ops::double(&mut two_alpha);
    unsafe {
        let zi = *z_initial.get_unchecked(acc.z_initial_idx);
        let mut eq = one_minus_alpha;
        let mut two_a_zi = two_alpha;
        field_ops::mul_assign(&mut two_a_zi, &zi);
        field_ops::add_assign(&mut eq, &two_a_zi);
        field_ops::sub_assign(&mut eq, &zi);
        field_ops::mul_assign(&mut acc.z_initial_prefactor, &eq);
        acc.z_initial_idx += 1;
    }
    let n = acc.pow_entries.len();
    let mut i = 0;
    while i < n {
        unsafe {
            let entry = acc.pow_entries.get_unchecked_mut(i);
            let s = entry.current_scalar;
            let mut eq = one_minus_alpha;
            let mut two_a_s = two_alpha;
            field_ops::mul_assign(&mut two_a_s, &s);
            field_ops::add_assign(&mut eq, &two_a_s);
            field_ops::sub_assign(&mut eq, &s);
            field_ops::mul_assign(&mut entry.prefactor, &eq);
            field_ops::square(&mut entry.current_scalar);
        }
        i += 1;
    }
}
#[inline(always)]
pub fn push_whir_pow_entry<const MAX_POW: usize>(
    acc: &mut ::verifier_common::whir::WhirAccumulator<BabyBearExt4, MAX_POW>,
    current_scalar: BabyBearExt4,
    coefficient: BabyBearExt4,
) {
    acc.pow_entries.push(::verifier_common::whir::WhirPowEntry {
        current_scalar,
        prefactor: BabyBearExt4::ONE,
        coefficient,
    });
}
#[inline(always)]
#[allow(clippy::too_many_arguments)]
pub unsafe fn process_oracle_query<
    I: NonDeterminismSource,
    E: ErrorCreator,
    const BUF_SIZE: usize,
    const LEAF_WORDS: usize,
>(
    hasher: &mut DelegatedBlake2sState,
    hash_buf: &mut ::verifier_common::blake2s_u32::AlignedArray64<
        core::mem::MaybeUninit<u32>,
        BUF_SIZE,
    >,
    num_columns: usize,
    query_index: usize,
    depth: usize,
    cap: &[u32],
    gamma_powers: &[BabyBearExt4],
    gamma_offset: usize,
    acc0: &mut BabyBearExt4,
    acc1: &mut BabyBearExt4,
    query: usize,
    nd_source: &mut I,
) -> Result<(), E::Error> {
    use verifier_common::whir::{hash_leaf_data_into_state, verify_merkle_path};
    let buf = hash_buf.assume_init_subarray_mut::<BUF_SIZE>();
    read_and_batch_leaf::<I>(
        &mut buf[..LEAF_WORDS],
        num_columns,
        gamma_powers,
        gamma_offset,
        acc0,
        acc1,
        nd_source,
    );
    let block_end =
        LEAF_WORDS.next_multiple_of(::verifier_common::blake2s_u32::BLAKE2S_BLOCK_SIZE_U32_WORDS);
    if block_end > LEAF_WORDS {
        hash_buf.zero_range(LEAF_WORDS, block_end);
    }
    let buf = hash_buf.assume_init_subarray::<BUF_SIZE>();
    hash_leaf_data_into_state(hasher, buf, LEAF_WORDS);
    if !verify_merkle_path::<I>(hasher, query_index, depth, cap, nd_source) {
        return Err(E::whir_merkle_path_failed(query));
    }
    Ok(())
}
