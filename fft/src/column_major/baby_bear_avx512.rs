//! EXPERIMENTAL AVX-512 twin of the BabyBear DIT NTT kernel in
//! [`super::baby_bear_avx2`]: the same blocked structure (fused AVX2 prep
//! sweep, block-local phase with 2^14 quarter-blocks, radix-16 line-complete
//! global sweeps) on 16-lane `__m512i` vectors — a 64-byte line is ONE
//! vector, so every line item is a single vector per stream, and the four
//! smallest levels (`ppg = 1, 2, 4, 8`) are in-register passes built on
//! `vpermt2d`. Values are identical to the AVX2 kernel (canonical Montgomery
//! everywhere). Functions are gated by `#[target_feature(enable = "avx512f")]`
//! so the enclosing binary keeps its plain AVX2 code generation; callers must
//! check `is_x86_feature_detected!("avx512f")`.
#![cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
#![allow(clippy::missing_safety_doc)]

use super::baby_bear_avx2::{balanced_chunk, spawn_chunk, Avx2TwiddleExt};
use core::arch::x86_64::*;
use field::baby_bear::base::BabyBearField;
use worker::Worker;

pub const P: u32 = 0x78000001;
pub const K: u32 = 0x77ffffff;

#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn pv() -> __m512i {
    _mm512_set1_epi32(P as i32)
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn kv() -> __m512i {
    _mm512_set1_epi32(K as i32)
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn ld(p: *const u32) -> __m512i {
    _mm512_loadu_si512(p as *const __m512i)
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn st(p: *mut u32, v: __m512i) {
    _mm512_storeu_si512(p as *mut __m512i, v)
}

/// Canonical Montgomery product on 16 lanes (even/odd 64-bit products,
/// high words merged with a lane mask, one conditional subtract).
#[inline]
#[target_feature(enable = "avx512f")]
pub unsafe fn mont_mul(a: __m512i, b: __m512i) -> __m512i {
    let lo = _mm512_mullo_epi32(a, b);
    let m = _mm512_mullo_epi32(lo, kv());
    let prod_e = _mm512_mul_epu32(a, b);
    let prod_o = _mm512_mul_epu32(_mm512_srli_epi64::<32>(a), _mm512_srli_epi64::<32>(b));
    let mp_e = _mm512_mul_epu32(m, pv());
    let mp_o = _mm512_mul_epu32(_mm512_srli_epi64::<32>(m), pv());
    let t_e = _mm512_add_epi64(prod_e, mp_e);
    let t_o = _mm512_add_epi64(prod_o, mp_o);
    let r = _mm512_mask_blend_epi32(0xAAAA, _mm512_srli_epi64::<32>(t_e), t_o);
    let rs = _mm512_sub_epi32(r, pv());
    _mm512_min_epu32(r, rs)
}
#[inline]
#[target_feature(enable = "avx512f")]
pub unsafe fn add(a: __m512i, b: __m512i) -> __m512i {
    let s = _mm512_add_epi32(a, b);
    _mm512_min_epu32(s, _mm512_sub_epi32(s, pv()))
}
#[inline]
#[target_feature(enable = "avx512f")]
pub unsafe fn sub(a: __m512i, b: __m512i) -> __m512i {
    let d = _mm512_sub_epi32(a, b);
    _mm512_min_epu32(d, _mm512_add_epi32(d, pv()))
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn butterfly(u: __m512i, v: __m512i, s: __m512i) -> (__m512i, __m512i) {
    (add(u, v), mont_mul(sub(u, v), s))
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn redc64(t_e: __m512i, t_o: __m512i) -> __m512i {
    let m_e = _mm512_mullo_epi32(t_e, kv());
    let m_o = _mm512_mullo_epi32(t_o, kv());
    let s_e = _mm512_add_epi64(t_e, _mm512_mul_epu32(m_e, pv()));
    let s_o = _mm512_add_epi64(t_o, _mm512_mul_epu32(m_o, pv()));
    let r = _mm512_mask_blend_epi32(0xAAAA, _mm512_srli_epi64::<32>(s_e), s_o);
    let rs = _mm512_sub_epi32(r, pv());
    _mm512_min_epu32(r, rs)
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn widening_mul(a: __m512i, b: __m512i) -> (__m512i, __m512i) {
    (
        _mm512_mul_epu32(a, b),
        _mm512_mul_epu32(_mm512_srli_epi64::<32>(a), _mm512_srli_epi64::<32>(b)),
    )
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn bias_all(bo: u32) -> __m512i {
    _mm512_set1_epi64(((P as u64) * (bo as u64)) as i64)
}

/// Radix-4 DIT core with u64 accumulation (identical to the AVX2 one).
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn fwd_core(
    x0: __m512i,
    x1: __m512i,
    x2: __m512i,
    x3: __m512i,
    s_a: __m512i,
    s_b: __m512i,
    s_o: __m512i,
    s_ao: __m512i,
    s_bo: __m512i,
    bias: __m512i,
) -> (__m512i, __m512i, __m512i, __m512i) {
    let y0 = add(x0, x1);
    let y2 = add(x2, x3);
    let z0 = add(y0, y2);
    let z2 = mont_mul(sub(y0, y2), s_o);
    let d01 = sub(x0, x1);
    let d23 = sub(x2, x3);
    let (p1e, p1o) = widening_mul(d01, s_a);
    let (p2e, p2o) = widening_mul(d23, s_b);
    let z1 = redc64(_mm512_add_epi64(p1e, p2e), _mm512_add_epi64(p1o, p2o));
    let (p3e, p3o) = widening_mul(d01, s_ao);
    let (p4e, p4o) = widening_mul(d23, s_bo);
    let z3 = redc64(
        _mm512_sub_epi64(_mm512_add_epi64(p3e, bias), p4e),
        _mm512_sub_epi64(_mm512_add_epi64(p3o, bias), p4o),
    );
    (z0, z1, z2, z3)
}

#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn twset(tw: *const u32, ao: *const u32, bo: *const u32, k2: usize) -> [__m512i; 6] {
    [
        _mm512_set1_epi32(*tw.add(2 * k2) as i32),
        _mm512_set1_epi32(*tw.add(2 * k2 + 1) as i32),
        _mm512_set1_epi32(*tw.add(k2) as i32),
        _mm512_set1_epi32(*ao.add(k2) as i32),
        _mm512_set1_epi32(*bo.add(k2) as i32),
        bias_all(*bo.add(k2)),
    ]
}

/// In-register pass for `ppg = 2^b`, `b <= 3`, over 32 consecutive elements
/// per iteration: `vpermt2d` de-interleaves the lo/hi halves of every pair,
/// the butterfly runs on 16 lanes, `vpermt2d` re-interleaves. `tw` points at
/// the group-index-offset twiddles for this block.
#[target_feature(enable = "avx512f")]
unsafe fn pass_small(a: *mut u32, n: usize, b: u32, tw: *const u32) {
    let ppg = 1usize << b;
    let mut idx_u = [0i32; 16];
    let mut idx_v = [0i32; 16];
    let mut idx_o0 = [0i32; 16];
    let mut idx_o1 = [0i32; 16];
    let mut dup = [0i32; 16];
    for l in 0..16usize {
        let iu = ((l >> b) << (b + 1)) | (l & (ppg - 1));
        idx_u[l] = iu as i32;
        idx_v[l] = (iu + ppg) as i32;
        dup[l] = (l >> b) as i32;
    }
    for i in 0..32usize {
        let lane = ((i >> (b + 1)) << b) | (i & (ppg - 1));
        let src = if (i >> b) & 1 == 1 { 16 } else { 0 };
        let v = (src + lane) as i32;
        if i < 16 {
            idx_o0[i] = v;
        } else {
            idx_o1[i - 16] = v;
        }
    }
    let idx_u = _mm512_loadu_si512(idx_u.as_ptr() as *const __m512i);
    let idx_v = _mm512_loadu_si512(idx_v.as_ptr() as *const __m512i);
    let idx_o0 = _mm512_loadu_si512(idx_o0.as_ptr() as *const __m512i);
    let idx_o1 = _mm512_loadu_si512(idx_o1.as_ptr() as *const __m512i);
    let dup = _mm512_loadu_si512(dup.as_ptr() as *const __m512i);
    let tw_per_iter = 16 >> b; // distinct twiddles per 32 elements
    let mut j = 0usize;
    while j < n {
        let v0 = ld(a.add(j));
        let v1 = ld(a.add(j + 16));
        let u = _mm512_permutex2var_epi32(v0, idx_u, v1);
        let v = _mm512_permutex2var_epi32(v0, idx_v, v1);
        // twiddles: `tw_per_iter` consecutive entries at group index j / (2 ppg), duplicated per lane group
        let t = _mm512_maskz_loadu_epi32(
            ((1u32 << tw_per_iter) - 1) as u16,
            tw.add(j >> (b + 1)) as *const i32,
        );
        let s = _mm512_permutexvar_epi32(dup, t);
        let (na, nb) = butterfly(u, v, s);
        st(a.add(j), _mm512_permutex2var_epi32(na, idx_o0, nb));
        st(a.add(j + 16), _mm512_permutex2var_epi32(na, idx_o1, nb));
        j += 32;
    }
}

/// Radix-4 items (`ppg >= 16`): item `t` = group `k2 = t / (ppg/16)`, vector `j16`.
#[target_feature(enable = "avx512f")]
pub unsafe fn radix4_items(
    a: *mut u32,
    ppg: usize,
    tw: *const u32,
    ao: *const u32,
    bo: *const u32,
    k2_offset: usize,
    item_range: core::ops::Range<usize>,
) {
    let vecs = ppg / 16;
    let mut t = item_range.start;
    while t < item_range.end {
        let k2 = t / vecs;
        let j16 = t % vecs;
        let [s_a, s_b, s_o, s_ao, s_bo, bias] = twset(tw, ao, bo, k2 + k2_offset);
        let run = (vecs - j16).min(item_range.end - t);
        let mut j = k2 * ppg * 4 + j16 * 16;
        for _ in 0..run {
            let (z0, z1, z2, z3) = fwd_core(
                ld(a.add(j)),
                ld(a.add(j + ppg)),
                ld(a.add(j + 2 * ppg)),
                ld(a.add(j + 3 * ppg)),
                s_a,
                s_b,
                s_o,
                s_ao,
                s_bo,
                bias,
            );
            st(a.add(j), z0);
            st(a.add(j + ppg), z1);
            st(a.add(j + 2 * ppg), z2);
            st(a.add(j + 3 * ppg), z3);
            j += 16;
        }
        t += run;
    }
}

/// Radix-2 items (`ppg >= 16`).
#[target_feature(enable = "avx512f")]
pub unsafe fn radix2_items(
    a: *mut u32,
    ppg: usize,
    tw: *const u32,
    k_offset: usize,
    item_range: core::ops::Range<usize>,
) {
    let vecs = ppg / 16;
    let mut t = item_range.start;
    while t < item_range.end {
        let k = t / vecs;
        let j16 = t % vecs;
        let s = _mm512_set1_epi32(*tw.add(k + k_offset) as i32);
        let run = (vecs - j16).min(item_range.end - t);
        let mut j = k * ppg * 2 + j16 * 16;
        for _ in 0..run {
            let (nu, nv) = butterfly(ld(a.add(j)), ld(a.add(j + ppg)), s);
            st(a.add(j), nu);
            st(a.add(j + ppg), nv);
            j += 16;
        }
        t += run;
    }
}

#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn radix16_core(x: &mut [__m512i; 16], twa: &[[__m512i; 6]; 4], twb: &[__m512i; 6]) {
    for q in 0..4 {
        let [s_a, s_b, s_o, s_ao, s_bo, bias] = twa[q];
        let (z0, z1, z2, z3) = fwd_core(
            x[4 * q],
            x[4 * q + 1],
            x[4 * q + 2],
            x[4 * q + 3],
            s_a,
            s_b,
            s_o,
            s_ao,
            s_bo,
            bias,
        );
        x[4 * q] = z0;
        x[4 * q + 1] = z1;
        x[4 * q + 2] = z2;
        x[4 * q + 3] = z3;
    }
    let [s_a, s_b, s_o, s_ao, s_bo, bias] = *twb;
    for i in 0..4 {
        let (z0, z1, z2, z3) = fwd_core(
            x[i],
            x[4 + i],
            x[8 + i],
            x[12 + i],
            s_a,
            s_b,
            s_o,
            s_ao,
            s_bo,
            bias,
        );
        x[i] = z0;
        x[4 + i] = z1;
        x[8 + i] = z2;
        x[12 + i] = z3;
    }
}

/// Radix-16 line items (`ppg >= 16`): one vector per stream per item.
#[target_feature(enable = "avx512f")]
pub unsafe fn radix16_items(
    a: *mut u32,
    ppg: usize,
    tw: *const u32,
    ao: *const u32,
    bo: *const u32,
    k4_offset: usize,
    item_range: core::ops::Range<usize>,
) {
    let lines = ppg / 16;
    let mut t = item_range.start;
    while t < item_range.end {
        let k4 = t / lines;
        let jl = t % lines;
        let kg = k4 + k4_offset;
        let twa: [[__m512i; 6]; 4] = core::array::from_fn(|q| twset(tw, ao, bo, 4 * kg + q));
        let twb = twset(tw, ao, bo, kg);
        let run = (lines - jl).min(item_range.end - t);
        let mut j = k4 * ppg * 16 + jl * 16;
        for _ in 0..run {
            let mut x: [__m512i; 16] = core::array::from_fn(|i| ld(a.add(j + i * ppg)));
            radix16_core(&mut x, &twa, &twb);
            for i in 0..16 {
                st(a.add(j + i * ppg), x[i]);
            }
            j += 16;
        }
        t += run;
    }
}

#[target_feature(enable = "avx512f")]
unsafe fn tail_two_groups_items(
    a: *mut u32,
    n: usize,
    tw: *const u32,
    j16_range: core::ops::Range<usize>,
) {
    let q = n / 4;
    let s_a = _mm512_set1_epi32(*tw as i32);
    let s_b = _mm512_set1_epi32(*tw.add(1) as i32);
    for j16 in j16_range {
        let j = j16 * 16;
        let (y0, y1) = butterfly(ld(a.add(j)), ld(a.add(j + q)), s_a);
        let (y2, y3) = butterfly(ld(a.add(j + 2 * q)), ld(a.add(j + 3 * q)), s_b);
        st(a.add(j), add(y0, y2));
        st(a.add(j + 2 * q), sub(y0, y2));
        st(a.add(j + q), add(y1, y3));
        st(a.add(j + 3 * q), sub(y1, y3));
    }
}
#[target_feature(enable = "avx512f")]
unsafe fn tail_final_items(a: *mut u32, n: usize, j16_range: core::ops::Range<usize>) {
    let half = n / 2;
    for j16 in j16_range {
        let j = j16 * 16;
        let u = ld(a.add(j));
        let v = ld(a.add(j + half));
        st(a.add(j), add(u, v));
        st(a.add(j + half), sub(u, v));
    }
}

pub const BLOCK_LOG2: u32 = 16;
pub const SUB_BLOCK_LOG2: u32 = 14;

/// Block-local levels (`ppg = 1 .. 2^15`) of the `b`-th 2^16 block, hierarchically
/// over 2^14 quarter-blocks: in-register passes 1/2/4/8, radix-16 (16..128),
/// radix-16 (256..2048), radix-4 (4096, 8192); then radix-4 (16384, 32768) over the block.
#[target_feature(enable = "avx512f")]
pub unsafe fn ntt_block_local(
    a: *mut u32,
    b: usize,
    tw: *const u32,
    ao: *const u32,
    bo: *const u32,
) {
    let blk = 1usize << BLOCK_LOG2;
    let sub = 1usize << SUB_BLOCK_LOG2;
    for q in 0..4 {
        let sb = 4 * b + q;
        let p = a.add(q * sub);
        for lvl in 0..4u32 {
            pass_small(p, sub, lvl, tw.add(sb * (sub >> (lvl + 1))));
        }
        radix16_items(p, 16, tw, ao, bo, sb * (sub / 256), 0..sub / 256);
        radix16_items(p, 256, tw, ao, bo, sb * (sub / 4096), 0..sub / 4096 * 16);
        radix4_items(
            p,
            4096,
            tw,
            ao,
            bo,
            sb * (sub / 16384),
            0..(sub / 16384) * 256,
        );
    }
    radix4_items(
        a,
        sub,
        tw,
        ao,
        bo,
        b * (blk / (4 * sub)),
        0..(blk / (4 * sub)) * (sub / 16),
    );
}

/// Blocked worker-parallel DIT NTT (`n >= 2^16`, bit-reversed -> natural), AVX-512.
#[target_feature(enable = "avx512f")]
pub unsafe fn ntt_bitrev_to_natural_blocked_parallel(
    a: &mut [u32],
    log_n: u32,
    tw: &[u32],
    tw_ao: &[u32],
    tw_bo: &[u32],
    worker: &Worker,
) {
    let n = a.len();
    let blk = 1usize << BLOCK_LOG2;
    debug_assert!(n >= blk && n == 1usize << log_n);
    let base_addr = a.as_mut_ptr() as usize;
    let (t_addr, ao_addr, bo_addr) = (
        tw.as_ptr() as usize,
        tw_ao.as_ptr() as usize,
        tw_bo.as_ptr() as usize,
    );
    let num_blocks = n / blk;
    worker.scope(num_blocks, |scope, geometry| {
        let (work, chunks) = (num_blocks, geometry.len());
        for idx in 0..chunks {
            let (start, size) = balanced_chunk(work, chunks, idx);
            spawn_chunk(scope, idx == chunks - 1, move |_| {
                for b in start..start + size {
                    ntt_block_local(
                        (base_addr as *mut u32).add(b * blk),
                        b,
                        t_addr as *const u32,
                        ao_addr as *const u32,
                        bo_addr as *const u32,
                    );
                }
            });
        }
    });
    let mut ppg = blk;
    let mut levels_left = log_n - BLOCK_LOG2;
    while levels_left >= 4 {
        let items = n / 256;
        let cur = ppg;
        worker.scope(items, |scope, geometry| {
            let (work, chunks) = (items, geometry.len());
            for idx in 0..chunks {
                let (start, size) = balanced_chunk(work, chunks, idx);
                spawn_chunk(scope, idx == chunks - 1, move |_| {
                    radix16_items(
                        base_addr as *mut u32,
                        cur,
                        t_addr as *const u32,
                        ao_addr as *const u32,
                        bo_addr as *const u32,
                        0,
                        start..start + size,
                    );
                });
            }
        });
        ppg *= 16;
        levels_left -= 4;
    }
    if levels_left == 3 {
        let items = n / 64;
        let cur = ppg;
        worker.scope(items, |scope, geometry| {
            let (work, chunks) = (items, geometry.len());
            for idx in 0..chunks {
                let (start, size) = balanced_chunk(work, chunks, idx);
                spawn_chunk(scope, idx == chunks - 1, move |_| {
                    radix4_items(
                        base_addr as *mut u32,
                        cur,
                        t_addr as *const u32,
                        ao_addr as *const u32,
                        bo_addr as *const u32,
                        0,
                        start..start + size,
                    );
                });
            }
        });
        levels_left = 1;
    }
    match levels_left {
        0 => {}
        2 => worker.scope(n / 64, |scope, geometry| {
            let (work, chunks) = (n / 64, geometry.len());
            for idx in 0..chunks {
                let (start, size) = balanced_chunk(work, chunks, idx);
                spawn_chunk(scope, idx == chunks - 1, move |_| {
                    tail_two_groups_items(
                        base_addr as *mut u32,
                        n,
                        t_addr as *const u32,
                        start..start + size,
                    );
                });
            }
        }),
        1 => worker.scope(n / 32, |scope, geometry| {
            let (work, chunks) = (n / 32, geometry.len());
            for idx in 0..chunks {
                let (start, size) = balanced_chunk(work, chunks, idx);
                spawn_chunk(scope, idx == chunks - 1, move |_| {
                    tail_final_items(base_addr as *mut u32, n, start..start + size);
                });
            }
        }),
        _ => unreachable!(),
    }
}

/// The AVX-512 coset LDE into a caller-provided buffer: the AVX2 fused prep
/// sweep, then the AVX-512 blocked NTT. Caller must have verified `avx512f`.
pub unsafe fn lde_coset_avx512_into(
    input: &[u32],
    offset: BabyBearField,
    tw: &[u32],
    ext: &Avx2TwiddleExt,
    out: &mut [u32],
    worker: &Worker,
) {
    let n = input.len();
    let log_n = n.trailing_zeros();
    assert!(n >= (1usize << BLOCK_LOG2) && out.len() == n);
    super::baby_bear_avx2::lde_prepare_bitrev_scaled_into(input, out, offset, worker);
    ntt_bitrev_to_natural_blocked_parallel(out, log_n, &tw[..n / 2], &ext.ao, &ext.bo, worker);
}

/// The AVX-512 coset LDE with a `Vec` output: see [`lde_coset_avx512_into`].
pub unsafe fn lde_coset_avx512_parallel(
    input: &[BabyBearField],
    offset: BabyBearField,
    twiddles: &[BabyBearField],
    ext: &Avx2TwiddleExt,
    worker: &Worker,
) -> Vec<BabyBearField> {
    let n = input.len();
    let input_raw: &[u32] = core::slice::from_raw_parts(input.as_ptr() as *const u32, n);
    let tw_raw: &[u32] =
        core::slice::from_raw_parts(twiddles.as_ptr() as *const u32, twiddles.len());
    let mut v: Vec<u32> = Vec::with_capacity(n);
    #[allow(clippy::uninit_vec)]
    v.set_len(n);
    lde_coset_avx512_into(input_raw, offset, tw_raw, ext, &mut v, worker);
    core::mem::transmute::<Vec<u32>, Vec<BabyBearField>>(v)
}

// ------------------------------------------------------------------------
// hypercube evals -> monomial coefficients (AVX-512, blocked)
// ------------------------------------------------------------------------

/// `levels` (1..=4) "upper half minus lower half" levels with the smallest
/// stride `stride >= 16`, fused in registers over line items (one vector per
/// stream): group `k` spans `stride << levels` elements.
#[target_feature(enable = "avx512f")]
unsafe fn sub_levels_items(
    p: *mut u32,
    stride: usize,
    levels: u32,
    item_range: core::ops::Range<usize>,
) {
    let m_count = 1usize << levels;
    let lines = stride / 16;
    let mut t = item_range.start;
    while t < item_range.end {
        let k = t / lines;
        let jl = t % lines;
        let run = (lines - jl).min(item_range.end - t);
        let mut j = k * stride * m_count + jl * 16;
        for _ in 0..run {
            let mut v = [_mm512_setzero_si512(); 16];
            for m in 0..m_count {
                v[m] = ld(p.add(j + m * stride));
            }
            for b in 0..levels {
                let bit = 1usize << b;
                for m in 0..m_count {
                    if m & bit != 0 {
                        v[m] = sub(v[m], v[m ^ bit]);
                    }
                }
            }
            for m in 1..m_count {
                st(p.add(j + m * stride), v[m]);
            }
            j += 16;
        }
        t += run;
    }
}

/// In-register "hi -= lo" for stride `2^b`, `b <= 3`, over 32 consecutive
/// elements per iteration (same lane split as [`pass_small`]).
#[target_feature(enable = "avx512f")]
unsafe fn sub_small(a: *mut u32, n: usize, b: u32) {
    let ppg = 1usize << b;
    let mut idx_u = [0i32; 16];
    let mut idx_v = [0i32; 16];
    let mut idx_o0 = [0i32; 16];
    let mut idx_o1 = [0i32; 16];
    for l in 0..16usize {
        let iu = ((l >> b) << (b + 1)) | (l & (ppg - 1));
        idx_u[l] = iu as i32;
        idx_v[l] = (iu + ppg) as i32;
    }
    for i in 0..32usize {
        let lane = ((i >> (b + 1)) << b) | (i & (ppg - 1));
        let src = if (i >> b) & 1 == 1 { 16 } else { 0 };
        let v = (src + lane) as i32;
        if i < 16 {
            idx_o0[i] = v;
        } else {
            idx_o1[i - 16] = v;
        }
    }
    let idx_u = _mm512_loadu_si512(idx_u.as_ptr() as *const __m512i);
    let idx_v = _mm512_loadu_si512(idx_v.as_ptr() as *const __m512i);
    let idx_o0 = _mm512_loadu_si512(idx_o0.as_ptr() as *const __m512i);
    let idx_o1 = _mm512_loadu_si512(idx_o1.as_ptr() as *const __m512i);
    let mut j = 0usize;
    while j < n {
        let v0 = ld(a.add(j));
        let v1 = ld(a.add(j + 16));
        let u = _mm512_permutex2var_epi32(v0, idx_u, v1);
        let v = _mm512_permutex2var_epi32(v0, idx_v, v1);
        let nv = sub(v, u);
        st(a.add(j), _mm512_permutex2var_epi32(u, idx_o0, nv));
        st(a.add(j + 16), _mm512_permutex2var_epi32(u, idx_o1, nv));
        j += 32;
    }
}

/// Transform of the 16 block-local variables of one 2^16 block (in cache):
/// three 4-level sweeps for strides 2^15..2^4, then strides 8/4/2/1 in
/// registers.
#[target_feature(enable = "avx512f")]
unsafe fn transform_block(a: *mut u32) {
    let blk = 1usize << 16;
    let mut stride = 1usize << 12;
    for _ in 0..3 {
        let group = stride << 4;
        sub_levels_items(a, stride, 4, 0..(blk / group) * (stride / 16));
        stride >>= 4;
    }
    debug_assert_eq!(stride, 1); // sweeps used strides 2^12, 2^8, 2^4
    for b in (0..4u32).rev() {
        sub_small(a, blk, b);
    }
}

/// Worker-parallel, out-of-place hypercube -> monomial transform on 16-lane
/// vectors: block-local phase (copy + 16 variables in cache), then the high
/// strides in 4-level sweeps. Byte-identical to the scalar reference.
#[target_feature(enable = "avx512f")]
pub unsafe fn transform_avx512_into(src: &[u32], dst: &mut [u32], size_log2: u32, worker: &Worker) {
    let len = 1usize << size_log2;
    assert_eq!(src.len(), len);
    assert_eq!(dst.len(), len);
    assert!(size_log2 >= 16);
    let blk = 1usize << 16;
    let num_blocks = len / blk;
    let (s_addr, d_addr) = (src.as_ptr() as usize, dst.as_mut_ptr() as usize);
    worker.scope(num_blocks, |scope, geometry| {
        let (work, chunks) = (num_blocks, geometry.len());
        for idx in 0..chunks {
            let (start, size) = balanced_chunk(work, chunks, idx);
            spawn_chunk(scope, idx == chunks - 1, move |_| {
                for b in start..start + size {
                    let d = (d_addr as *mut u32).add(b * blk);
                    core::ptr::copy_nonoverlapping((s_addr as *const u32).add(b * blk), d, blk);
                    transform_block(d);
                }
            });
        }
    });
    let mut stride = blk;
    let mut levels_left = size_log2 - 16;
    while levels_left > 0 {
        let levels = levels_left.min(4);
        let group = stride << levels;
        let items = (len / group) * (stride / 16);
        worker.scope(items, |scope, geometry| {
            let (work, chunks) = (items, geometry.len());
            for idx in 0..chunks {
                let (start, size) = balanced_chunk(work, chunks, idx);
                spawn_chunk(scope, idx == chunks - 1, move |_| {
                    sub_levels_items(d_addr as *mut u32, stride, levels, start..start + size);
                });
            }
        });
        stride = group;
        levels_left -= levels;
    }
}

/// [`transform_avx512_into`] with a fresh `Vec` output.
pub unsafe fn transform_avx512(src: &[u32], size_log2: u32, worker: &Worker) -> Vec<u32> {
    let len = 1usize << size_log2;
    let mut dst: Vec<u32> = Vec::with_capacity(len);
    #[allow(clippy::uninit_vec)]
    dst.set_len(len);
    transform_avx512_into(src, &mut dst, size_log2, worker);
    dst
}

// ------------------------------------------------------------------------
// fused scale + bit-reverse + block-local phase
// ------------------------------------------------------------------------

/// `offset^i = lo[i & mask] * hi[i >> h]` split tables (raw Montgomery).
pub struct SplitPowers {
    pub lo: Vec<u32>,
    pub hi: Vec<u32>,
    pub h: u32,
    pub mask: usize,
}
impl SplitPowers {
    pub fn new(offset: BabyBearField, log_n: u32) -> Self {
        use field::Field;
        let h = log_n / 2;
        let mut lo = Vec::with_capacity(1 << h);
        let mut x = BabyBearField::ONE;
        for _ in 0..(1usize << h) {
            lo.push(x.raw_u32_value());
            x.mul_assign(&offset);
        }
        // x == offset^(2^h)
        let step = x;
        let mut hi = Vec::with_capacity(1 << (log_n - h));
        let mut y = BabyBearField::ONE;
        for _ in 0..(1usize << (log_n - h)) {
            hi.push(y.raw_u32_value());
            y.mul_assign(&step);
        }
        Self {
            lo,
            hi,
            h,
            mask: (1usize << h) - 1,
        }
    }
}

/// 16x16 transpose of `u32` lanes: four 8x8 transposes on the 256-bit
/// halves, recombined.
#[target_feature(enable = "avx512f")]
unsafe fn transpose_16x16(r: &mut [__m512i; 16]) {
    use super::baby_bear_avx2::avx2::transpose_8x8;
    let mut a0: [__m256i; 8] = core::array::from_fn(|i| _mm512_extracti64x4_epi64::<0>(r[i]));
    let mut a1: [__m256i; 8] = core::array::from_fn(|i| _mm512_extracti64x4_epi64::<0>(r[8 + i]));
    let mut b0: [__m256i; 8] = core::array::from_fn(|i| _mm512_extracti64x4_epi64::<1>(r[i]));
    let mut b1: [__m256i; 8] = core::array::from_fn(|i| _mm512_extracti64x4_epi64::<1>(r[8 + i]));
    transpose_8x8(&mut a0);
    transpose_8x8(&mut a1);
    transpose_8x8(&mut b0);
    transpose_8x8(&mut b1);
    for c in 0..8 {
        r[c] = _mm512_inserti64x4::<1>(_mm512_castsi256_si512(a0[c]), a1[c]);
        r[8 + c] = _mm512_inserti64x4::<1>(_mm512_castsi256_si512(b0[c]), b1[c]);
    }
}

const REV4: [usize; 16] = [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15];

/// One 16-block group `c` (blocks `c + 16*s`, `s < 16`, of a 2^24 coset):
/// gather the scaled, bit-reversed inputs of all 16 blocks into `bufs`
/// (16 x 256 KB) by 16-line tiles (16 random full source lines -> one
/// 16x16 transpose -> 16 full lines, one per block), run the block-local
/// NTT on each block while it is cache-resident, copy each block out once.
#[target_feature(enable = "avx512f")]
unsafe fn fused_group(
    src: *const u32,
    out: *mut u32,
    c: usize,
    sp: &SplitPowers,
    tw: *const u32,
    ao: *const u32,
    bo: *const u32,
    bufs: *mut u32,
    stream: bool,
) {
    let blk = 1usize << BLOCK_LOG2;
    let start = c * blk;
    let mut i0 = start;
    while i0 < start + blk {
        let mut rows = [_mm512_setzero_si512(); 16];
        for b in 0..16 {
            let g = (((i0 + b) as u32).reverse_bits() >> 12) as usize; // rev20
            let k0 = g * 16;
            let f = mont_mul(
                ld(sp.lo.as_ptr().add(k0 & sp.mask)),
                _mm512_set1_epi32(sp.hi[k0 >> sp.h] as i32),
            );
            rows[b] = mont_mul(ld(src.add(k0)), f);
        }
        transpose_16x16(&mut rows);
        for l in 0..16 {
            st(bufs.add(REV4[l] * blk + (i0 - start)), rows[l]);
        }
        i0 += 16;
    }
    for s in 0..16 {
        let b = c + 16 * s;
        let p = bufs.add(s * blk);
        ntt_block_local(p, b, tw, ao, bo);
        // copy-out: non-temporal full-line stores (no read-for-ownership) when
        // the destination is 64-byte aligned, plain copy otherwise
        let dst = out.add(b * blk);
        if stream {
            let mut q = 0usize;
            while q < blk {
                st_nt(dst.add(q), ld(p.add(q)));
                q += 16;
            }
        } else {
            core::ptr::copy_nonoverlapping(p, dst, blk);
        }
    }
    if stream {
        _mm_sfence();
    }
}

thread_local! {
    /// Reusable page-aligned gather buffer per worker thread (16 padded blocks):
    /// allocating and zeroing it per coset call cost a full sweep of page faults.
    static GROUP_BUFS: core::cell::RefCell<Option<AlignedU32>> = const { core::cell::RefCell::new(None) };
}

/// Runs `f` with this thread's gather buffer (at least `min_len` elements).
fn with_group_buf<R>(min_len: usize, f: impl FnOnce(usize) -> R) -> R {
    GROUP_BUFS.with(|cell| {
        let mut b = cell.borrow_mut();
        if b.as_ref().map_or(true, |x| x.len() < min_len) {
            *b = Some(AlignedU32::zeroed(min_len));
        }
        f(b.as_mut().unwrap().as_mut_ptr() as usize)
    })
}

/// Global phase (levels above the block) of the AVX-512 kernel.
#[target_feature(enable = "avx512f")]
pub unsafe fn phase_b_global(
    a: &mut [u32],
    log_n: u32,
    tw: &[u32],
    tw_ao: &[u32],
    tw_bo: &[u32],
    worker: &Worker,
) {
    let n = a.len();
    let blk = 1usize << BLOCK_LOG2;
    let base_addr = a.as_mut_ptr() as usize;
    let (t_addr, ao_addr, bo_addr) = (
        tw.as_ptr() as usize,
        tw_ao.as_ptr() as usize,
        tw_bo.as_ptr() as usize,
    );
    let mut ppg = blk;
    let mut levels_left = log_n - BLOCK_LOG2;
    while levels_left >= 4 {
        let items = n / 256;
        let cur = ppg;
        worker.scope(items, |scope, geometry| {
            let (work, chunks) = (items, geometry.len());
            for idx in 0..chunks {
                let (start, size) = balanced_chunk(work, chunks, idx);
                spawn_chunk(scope, idx == chunks - 1, move |_| {
                    radix16_items(
                        base_addr as *mut u32,
                        cur,
                        t_addr as *const u32,
                        ao_addr as *const u32,
                        bo_addr as *const u32,
                        0,
                        start..start + size,
                    );
                });
            }
        });
        ppg *= 16;
        levels_left -= 4;
    }
    assert_eq!(levels_left, 0, "fused kernel supports log_n = 16 + 4k");
}

/// The fused AVX-512 coset LDE for `n = 2^24` into a caller-provided buffer:
/// gather + block phase in one sweep (16-block groups), then the radix-16
/// global sweeps. Three DRAM sweeps per coset instead of four. `stream`
/// uses non-temporal copy-out stores (`out` must be 64-byte aligned).
pub unsafe fn lde_coset_avx512_fused_into(
    input: &[u32],
    offset: BabyBearField,
    tw: &[u32],
    ext: &Avx2TwiddleExt,
    out: &mut [u32],
    worker: &Worker,
    stream: bool,
) {
    let n = input.len();
    let log_n = n.trailing_zeros();
    assert_eq!(
        log_n, 24,
        "fused kernel is written for 2^24 (16-block groups)"
    );
    assert_eq!(out.len(), n);
    if stream {
        assert_eq!(
            out.as_ptr() as usize % 64,
            0,
            "streaming stores need a 64-byte aligned output"
        );
    }
    let sp = SplitPowers::new(offset, log_n);
    let (in_addr, out_addr) = (input.as_ptr() as usize, out.as_mut_ptr() as usize);
    let (t_addr, ao_addr, bo_addr) = (
        tw.as_ptr() as usize,
        ext.ao.as_ptr() as usize,
        ext.bo.as_ptr() as usize,
    );
    let sp = &sp;
    let groups = 16usize;
    worker.scope(groups, |scope, geometry| {
        let (work, chunks) = (groups, geometry.len());
        for idx in 0..chunks {
            let (start, size) = balanced_chunk(work, chunks, idx);
            spawn_chunk(scope, idx == chunks - 1, move |_| {
                with_group_buf(16 * BUF_BLOCK_STRIDE, |bufs| {
                    for c in start..start + size {
                        fused_group(
                            in_addr as *const u32,
                            out_addr as *mut u32,
                            c,
                            sp,
                            t_addr as *const u32,
                            ao_addr as *const u32,
                            bo_addr as *const u32,
                            bufs as *mut u32,
                            stream,
                        );
                    }
                });
            });
        }
    });
    phase_b_global(out, log_n, &tw[..n / 2], &ext.ao, &ext.bo, worker);
}

/// [`lde_coset_avx512_fused_into`] with a `Vec` output (plain copy-out stores).
pub unsafe fn lde_coset_avx512_fused(
    input: &[BabyBearField],
    offset: BabyBearField,
    twiddles: &[BabyBearField],
    ext: &Avx2TwiddleExt,
    worker: &Worker,
) -> Vec<BabyBearField> {
    let n = input.len();
    let input_raw: &[u32] = core::slice::from_raw_parts(input.as_ptr() as *const u32, n);
    let tw_raw: &[u32] =
        core::slice::from_raw_parts(twiddles.as_ptr() as *const u32, twiddles.len());
    let mut v: Vec<u32> = Vec::with_capacity(n);
    #[allow(clippy::uninit_vec)]
    v.set_len(n);
    lde_coset_avx512_fused_into(input_raw, offset, tw_raw, ext, &mut v, worker, false);
    core::mem::transmute::<Vec<u32>, Vec<BabyBearField>>(v)
}

// ------------------------------------------------------------------------
// aligned buffers (benchmark aid)
// ------------------------------------------------------------------------

/// 2 MB-aligned, uninitialised `u32` buffer: lets the kernels use aligned and
/// non-temporal (`_mm512_stream_si512`) stores, which need the 64-byte
/// alignment that a `Vec` (page + 16 under glibc malloc) does not provide,
/// and gives every buffer of 2 MB or more transparent huge pages in full
/// (measured: 4 KB-aligned 4 MB buffers get only 40% huge pages).
pub struct AlignedU32 {
    ptr: core::ptr::NonNull<u32>,
    len: usize,
}
unsafe impl Send for AlignedU32 {}
unsafe impl Sync for AlignedU32 {}
impl AlignedU32 {
    pub const ALIGN: usize = 2 << 20;
    fn layout(len: usize) -> std::alloc::Layout {
        std::alloc::Layout::from_size_align(len.max(1) * 4, Self::ALIGN).unwrap()
    }
    pub fn uninit(len: usize) -> Self {
        let ptr = unsafe { std::alloc::alloc(Self::layout(len)) } as *mut u32;
        Self {
            ptr: core::ptr::NonNull::new(ptr).expect("aligned allocation failed"),
            len,
        }
    }
    pub fn zeroed(len: usize) -> Self {
        let ptr = unsafe { std::alloc::alloc_zeroed(Self::layout(len)) } as *mut u32;
        Self {
            ptr: core::ptr::NonNull::new(ptr).expect("aligned allocation failed"),
            len,
        }
    }
}
impl core::ops::Deref for AlignedU32 {
    type Target = [u32];
    fn deref(&self) -> &[u32] {
        unsafe { core::slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }
}
impl core::ops::DerefMut for AlignedU32 {
    fn deref_mut(&mut self) -> &mut [u32] {
        unsafe { core::slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len) }
    }
}
impl Drop for AlignedU32 {
    fn drop(&mut self) {
        unsafe { std::alloc::dealloc(self.ptr.as_ptr() as *mut u8, Self::layout(self.len)) }
    }
}

/// Non-temporal full-line store (`p` must be 64-byte aligned).
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn st_nt(p: *mut u32, v: __m512i) {
    debug_assert_eq!(p as usize % 64, 0);
    _mm512_stream_si512(p as *mut _, v)
}

/// Gather-buffer block stride: 2^16 elements plus one line group of padding so
/// the 16 buffered blocks do not share L1/L2 cache sets.
pub const BUF_BLOCK_STRIDE: usize = (1 << BLOCK_LOG2) + 64;

// ------------------------------------------------------------------------
// strided pass: transform completion + coset scaling + first four DIF
// stages with chain-generated twiddles
// ------------------------------------------------------------------------
//
// Layout facts (N = 2^n, chunk = 2^(n-4), line = 16 elements):
// * The partially transformed monomials live in 16 chunks `chunk_stride`
//   apart; chunk `m` holds natural indices `i = i_lo + m * chunk`.
// * The kernel's DIT layout puts `c[i]` at position `rev_n(i)`, so the 16
//   values sharing `i_lo` (one per chunk) form ONE output line at
//   `rev_(n-4)(i_lo) * 16`, with `m` bit-reversed inside the line, and the
//   first four DIF stages (`ppg = 1, 2, 4, 8`) act inside that line: stage
//   `s` pairs streams `m` differing in bit `3-s` of `m`, with the twiddle
//   `omega^(2^s * (i_lo + chunk * (m mod 2^(3-s))))`, i.e. `t^(2^s)` times a
//   power of the 16th root `zeta = omega^chunk`, where `t = omega^i_lo` runs
//   along the lanes and is advanced by one broadcast multiply per line — no
//   twiddle table reads at all.
// * Reading line `L` (i_lo = 16 L .. 16 L + 15) of all 16 chunks is 16
//   sequential streams; after the transform completion (top four variables:
//   whole-vector subtractions), the scaling by `offset^i_lo * (offset^chunk)^m`,
//   the four butterfly stages and one 16x16 register transpose, lane `l` is
//   the full output line `rev4(l) * chunk + rev_(n-8)(L) * 16`.

/// Scalar power (Montgomery form in and out).
fn pow_f(mut base: BabyBearField, mut e: u64) -> BabyBearField {
    use field::Field;
    let mut acc = BabyBearField::ONE;
    while e > 0 {
        if e & 1 == 1 {
            acc.mul_assign(&base);
        }
        base.square();
        e >>= 1;
    }
    acc
}

fn rev_bits(x: usize, bits: u32) -> usize {
    if bits == 0 {
        0
    } else {
        ((x as u64).reverse_bits() >> (64 - bits)) as usize
    }
}

/// Per-pass constants of the strided pass (raw Montgomery values).
pub struct StridedConsts {
    pub omega: BabyBearField,
    pub offset: BabyBearField,
    omega_lanes: [u32; 16],
    offset_lanes: [u32; 16],
    hi: [u32; 16],
    zeta: [u32; 8],
}
impl StridedConsts {
    pub fn new(omega: BabyBearField, offset: BabyBearField, log_n: u32) -> Self {
        use field::Field;
        let chunk = 1u64 << (log_n - 4);
        let zeta = pow_f(omega, chunk);
        let hi_step = pow_f(offset, chunk);
        let mut omega_lanes = [0u32; 16];
        let mut offset_lanes = [0u32; 16];
        let mut hi = [0u32; 16];
        let mut zeta_pows = [0u32; 8];
        let (mut a, mut b, mut c, mut d) = (
            BabyBearField::ONE,
            BabyBearField::ONE,
            BabyBearField::ONE,
            BabyBearField::ONE,
        );
        for l in 0..16 {
            omega_lanes[l] = a.raw_u32_value();
            offset_lanes[l] = b.raw_u32_value();
            hi[l] = c.raw_u32_value();
            a.mul_assign(&omega);
            b.mul_assign(&offset);
            c.mul_assign(&hi_step);
        }
        for m in 0..8 {
            zeta_pows[m] = d.raw_u32_value();
            d.mul_assign(&zeta);
        }
        Self {
            omega,
            offset,
            omega_lanes,
            offset_lanes,
            hi,
            zeta: zeta_pows,
        }
    }
}

/// Broadcast lane/twiddle constants of one thread's strided loop.
struct StridedRegs {
    hi: [__m512i; 16],
    zeta: [__m512i; 8],
    ol: __m512i,
    sl: __m512i,
    tb: __m512i,
    sb: __m512i,
    tstep: __m512i,
    sstep: __m512i,
}
impl StridedRegs {
    /// Chain state starting at line `first_line`, advancing `lines_per_step` lines per step.
    #[target_feature(enable = "avx512f")]
    unsafe fn new(k: &StridedConsts, first_line: usize, lines_per_step: usize) -> Self {
        let tb = pow_f(k.omega, 16 * first_line as u64).raw_u32_value();
        let sb = pow_f(k.offset, 16 * first_line as u64).raw_u32_value();
        let tstep = pow_f(k.omega, 16 * lines_per_step as u64).raw_u32_value();
        let sstep = pow_f(k.offset, 16 * lines_per_step as u64).raw_u32_value();
        Self {
            hi: core::array::from_fn(|m| _mm512_set1_epi32(k.hi[m] as i32)),
            zeta: core::array::from_fn(|m| _mm512_set1_epi32(k.zeta[m] as i32)),
            ol: ld(k.omega_lanes.as_ptr()),
            sl: ld(k.offset_lanes.as_ptr()),
            tb: _mm512_set1_epi32(tb as i32),
            sb: _mm512_set1_epi32(sb as i32),
            tstep: _mm512_set1_epi32(tstep as i32),
            sstep: _mm512_set1_epi32(sstep as i32),
        }
    }
    #[inline]
    #[target_feature(enable = "avx512f")]
    unsafe fn advance(&mut self) {
        self.tb = mont_mul(self.tb, self.tstep);
        self.sb = mont_mul(self.sb, self.sstep);
    }
}

/// One tile: line `line` of all 16 chunks -> the 16 output lines (row `l` =
/// lane `l`, i.e. `i_lo = 16 line + l`), values in the kernel's DIT layout
/// with the first four stages applied.
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn strided_tile(
    part: *const u32,
    chunk_stride: usize,
    line: usize,
    r: &StridedRegs,
) -> [__m512i; 16] {
    let mut v: [__m512i; 16] = core::array::from_fn(|m| ld(part.add(m * chunk_stride + line * 16)));
    // transform completion: the top four variables (`hi -= lo` on the m bits)
    for b in 0..4 {
        let bit = 1usize << b;
        for m in 0..16 {
            if m & bit != 0 {
                v[m] = sub(v[m], v[m ^ bit]);
            }
        }
    }
    // coset scaling: offset^i = offset^i_lo * (offset^chunk)^m
    let sc = mont_mul(r.sb, r.sl);
    for m in 0..16 {
        v[m] = mont_mul(v[m], mont_mul(sc, r.hi[m]));
    }
    // DIF stages 0..3: twiddles t, t^2, t^4, t^8 times zeta powers
    let t = mont_mul(r.tb, r.ol);
    let t2 = mont_mul(t, t);
    let t4 = mont_mul(t2, t2);
    let t8 = mont_mul(t4, t4);
    for m in 0..8 {
        let w = if m == 0 { t } else { mont_mul(t, r.zeta[m]) };
        let (a, b) = butterfly(v[m], v[m + 8], w);
        v[m] = a;
        v[m + 8] = b;
    }
    let w1 = [
        t2,
        mont_mul(t2, r.zeta[2]),
        mont_mul(t2, r.zeta[4]),
        mont_mul(t2, r.zeta[6]),
    ];
    for base in [0usize, 8] {
        for m in 0..4 {
            let (a, b) = butterfly(v[base + m], v[base + m + 4], w1[m]);
            v[base + m] = a;
            v[base + m + 4] = b;
        }
    }
    let w2 = [t4, mont_mul(t4, r.zeta[4])];
    for base in [0usize, 4, 8, 12] {
        for m in 0..2 {
            let (a, b) = butterfly(v[base + m], v[base + m + 2], w2[m]);
            v[base + m] = a;
            v[base + m + 2] = b;
        }
    }
    for m in (0..16).step_by(2) {
        let (a, b) = butterfly(v[m], v[m + 1], t8);
        v[m] = a;
        v[m + 1] = b;
    }
    // rows in bit-reversed m order, then transpose: row l = output line of lane l
    let mut rows: [__m512i; 16] = core::array::from_fn(|i| v[REV4[i]]);
    transpose_16x16(&mut rows);
    rows
}

/// Hypercube -> monomial transform of the low `chunk_log2` variables only,
/// chunk by chunk (`2^chunk_log2` elements each, laid out `chunk_stride`
/// apart in `dst` so the strided pass's 16 read streams do not alias); the
/// top `size_log2 - chunk_log2` variables are left to the strided pass.
/// `chunk_local`: one task per chunk (block phase + chunk sweeps while the
/// chunk is cache-hot); otherwise all-thread sweeps.
#[target_feature(enable = "avx512f")]
pub unsafe fn transform_partial_chunked_into(
    src: &[u32],
    dst: &mut [u32],
    size_log2: u32,
    chunk_log2: u32,
    chunk_stride: usize,
    chunk_local: bool,
    worker: &Worker,
) {
    let len = 1usize << size_log2;
    assert_eq!(src.len(), len);
    assert!(chunk_log2 >= 16 && chunk_log2 <= size_log2);
    let chunk = 1usize << chunk_log2;
    let num_chunks = len / chunk;
    assert!(chunk_stride >= chunk && chunk_stride % 16 == 0);
    assert!(dst.len() >= (num_chunks - 1) * chunk_stride + chunk);
    let blk = 1usize << 16;
    let bpc = chunk / blk;
    let (s_addr, d_addr) = (src.as_ptr() as usize, dst.as_mut_ptr() as usize);
    let chunk_levels = chunk_log2 - 16;
    if chunk_local {
        worker.scope(num_chunks, |scope, geometry| {
            let (work, chunks) = (num_chunks, geometry.len());
            for idx in 0..chunks {
                let (start, size) = balanced_chunk(work, chunks, idx);
                spawn_chunk(scope, idx == chunks - 1, move |_| {
                    for c in start..start + size {
                        let d = (d_addr as *mut u32).add(c * chunk_stride);
                        let s = (s_addr as *const u32).add(c * chunk);
                        for b in 0..bpc {
                            core::ptr::copy_nonoverlapping(s.add(b * blk), d.add(b * blk), blk);
                            transform_block(d.add(b * blk));
                        }
                        let mut stride = blk;
                        let mut left = chunk_levels;
                        while left > 0 {
                            let levels = left.min(4);
                            let group = stride << levels;
                            sub_levels_items(d, stride, levels, 0..(chunk / group) * (stride / 16));
                            stride = group;
                            left -= levels;
                        }
                    }
                });
            }
        });
    } else {
        let num_blocks = len / blk;
        worker.scope(num_blocks, |scope, geometry| {
            let (work, chunks) = (num_blocks, geometry.len());
            for idx in 0..chunks {
                let (start, size) = balanced_chunk(work, chunks, idx);
                spawn_chunk(scope, idx == chunks - 1, move |_| {
                    for b in start..start + size {
                        let d =
                            (d_addr as *mut u32).add((b / bpc) * chunk_stride + (b % bpc) * blk);
                        core::ptr::copy_nonoverlapping((s_addr as *const u32).add(b * blk), d, blk);
                        transform_block(d);
                    }
                });
            }
        });
        let mut stride = blk;
        let mut left = chunk_levels;
        while left > 0 {
            let levels = left.min(4);
            let group = stride << levels;
            let per_chunk = (chunk / group) * (stride / 16);
            let items = num_chunks * per_chunk;
            worker.scope(items, |scope, geometry| {
                let (work, chunks) = (items, geometry.len());
                for idx in 0..chunks {
                    let (start, size) = balanced_chunk(work, chunks, idx);
                    spawn_chunk(scope, idx == chunks - 1, move |_| {
                        let mut t = start;
                        while t < start + size {
                            let c = t / per_chunk;
                            let lo = t % per_chunk;
                            let run = (per_chunk - lo).min(start + size - t);
                            sub_levels_items(
                                (d_addr as *mut u32).add(c * chunk_stride),
                                stride,
                                levels,
                                lo..lo + run,
                            );
                            t += run;
                        }
                    });
                }
            });
            stride = group;
            left -= levels;
        }
    }
}

/// Levels `ppg = 16 .. 2^13` of the 2^14 sub-block `sb` (in-register passes
/// already done).
#[target_feature(enable = "avx512f")]
pub unsafe fn ntt_sub_block_from16(
    p: *mut u32,
    sb: usize,
    tw: *const u32,
    ao: *const u32,
    bo: *const u32,
) {
    let sub = 1usize << SUB_BLOCK_LOG2;
    radix16_items(p, 16, tw, ao, bo, sb * (sub / 256), 0..sub / 256);
    radix16_items(p, 256, tw, ao, bo, sb * (sub / 4096), 0..sub / 4096 * 16);
    radix4_items(
        p,
        4096,
        tw,
        ao,
        bo,
        sb * (sub / 16384),
        0..(sub / 16384) * 256,
    );
}

/// Block-local levels `ppg = 16 .. 2^15` of block `b` (the in-register
/// passes `ppg = 1, 2, 4, 8` were done by the strided pass).
#[target_feature(enable = "avx512f")]
pub unsafe fn ntt_block_local_from16(
    a: *mut u32,
    b: usize,
    tw: *const u32,
    ao: *const u32,
    bo: *const u32,
) {
    let blk = 1usize << BLOCK_LOG2;
    let sub = 1usize << SUB_BLOCK_LOG2;
    for q in 0..4 {
        ntt_sub_block_from16(a.add(q * sub), 4 * b + q, tw, ao, bo);
    }
    radix4_items(
        a,
        sub,
        tw,
        ao,
        bo,
        b * (blk / (4 * sub)),
        0..(blk / (4 * sub)) * (sub / 16),
    );
}

/// Worker-parallel block-local phase from `ppg = 16` over the whole array.
pub unsafe fn block_local_from16_parallel(
    a: &mut [u32],
    tw: &[u32],
    ao: &[u32],
    bo: &[u32],
    worker: &Worker,
    block_stride: usize,
) {
    block_local_parallel(a, tw, ao, bo, worker, true, block_stride)
}

/// Worker-parallel block-local phase over the whole array (block `b` at
/// `b * block_stride`): all block-local levels (`from16 == false`) or only
/// `ppg >= 16` (`from16 == true`).
pub unsafe fn block_local_parallel(
    a: &mut [u32],
    tw: &[u32],
    ao: &[u32],
    bo: &[u32],
    worker: &Worker,
    from16: bool,
    block_stride: usize,
) {
    let blk = 1usize << BLOCK_LOG2;
    assert!(block_stride >= blk);
    let num_blocks = a.len() / block_stride;
    let base_addr = a.as_mut_ptr() as usize;
    let (t_addr, ao_addr, bo_addr) = (
        tw.as_ptr() as usize,
        ao.as_ptr() as usize,
        bo.as_ptr() as usize,
    );
    worker.scope(num_blocks, |scope, geometry| {
        let (work, chunks) = (num_blocks, geometry.len());
        for idx in 0..chunks {
            let (start, size) = balanced_chunk(work, chunks, idx);
            spawn_chunk(scope, idx == chunks - 1, move |_| {
                for b in start..start + size {
                    let p = (base_addr as *mut u32).add(b * block_stride);
                    let (t, o, q) = (
                        t_addr as *const u32,
                        ao_addr as *const u32,
                        bo_addr as *const u32,
                    );
                    if from16 {
                        ntt_block_local_from16(p, b, t, o, q);
                    } else {
                        ntt_block_local(p, b, t, o, q);
                    }
                }
            });
        }
    });
}

/// Strided pass over `line_range`, output lines written straight to `out`
/// (16 full random lines per tile; non-temporal when `stream`).
#[target_feature(enable = "avx512f")]
unsafe fn strided_lines_to_out(
    part: *const u32,
    chunk_stride: usize,
    out: *mut u32,
    log_n: u32,
    line_range: core::ops::Range<usize>,
    k: &StridedConsts,
    stream: bool,
    out_block_stride: usize,
) {
    let chunk = 1usize << (log_n - 4);
    let lines_log2 = log_n - 8;
    let blk = 1usize << BLOCK_LOG2;
    let mut regs = StridedRegs::new(k, line_range.start, 1);
    for line in line_range {
        let rows = strided_tile(part, chunk_stride, line, &regs);
        let rl = rev_bits(line, lines_log2);
        for l in 0..16 {
            let o = REV4[l] * chunk + rl * 16;
            let dst = out.add((o / blk) * out_block_stride + (o % blk));
            if stream {
                st_nt(dst, rows[l]);
            } else {
                st(dst, rows[l]);
            }
        }
        regs.advance();
    }
    if stream {
        _mm_sfence();
    }
}

/// Options of the strided pipelines.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct StridedCfg {
    /// Non-temporal full-line stores (needs 64-byte aligned buffers).
    pub stream: bool,
    /// Radix-256 global pass instead of the two radix-16 sweeps.
    pub r256: bool,
    /// Output block stride: `2^16` (contiguous) or `2^16 + 64` (padded, so the
    /// 256 streams of a radix-256 item sit in distinct L2 sets).
    pub out_block_stride: usize,
    /// Radix-256: consecutive lines per stream handled per L2-resident group
    /// (1..=4; 4 makes every stream access a 256-byte run).
    pub group: usize,
    /// Radix-256: software-prefetch the next group into L2 during the compute.
    pub prefetch: bool,
    /// Gather block size: 16 (2^16 blocks, 4 MB group buffers, radix-256
    /// global pass) or 14 (2^14 blocks, 1 MB group buffers, radix-1024).
    pub blk_log2: u32,
}

/// Padded output block stride: 2^16 elements plus one 256-byte line group.
pub const OUT_BLOCK_STRIDE_PADDED: usize = (1 << BLOCK_LOG2) + 64;

/// Length of an output buffer in the layout with the given block size and stride.
pub const fn out_len(log_n: u32, blk_log2: u32, out_block_stride: usize) -> usize {
    (1 << (log_n - blk_log2)) * out_block_stride
}

fn check_strided_args(
    part: &[u32],
    chunk_stride: usize,
    log_n: u32,
    out: &[u32],
    cfg: &StridedCfg,
) {
    let n = 1usize << log_n;
    assert!(log_n >= 20);
    assert!(part.len() >= 15 * chunk_stride + (n >> 4));
    assert!(cfg.blk_log2 == 16 || cfg.blk_log2 == 14);
    assert!(cfg.out_block_stride >= (1 << cfg.blk_log2) && cfg.out_block_stride % 16 == 0);
    assert_eq!(
        out.len(),
        out_len(log_n, cfg.blk_log2, cfg.out_block_stride)
    );
    assert!(
        cfg.r256 || cfg.blk_log2 == 14 || cfg.out_block_stride == (1 << BLOCK_LOG2),
        "the radix-16 global sweeps need the contiguous layout"
    );
    if cfg.stream {
        assert_eq!(
            out.as_ptr() as usize % 64,
            0,
            "streaming stores need a 64-byte aligned output"
        );
    }
}

/// Coset LDE from the partially transformed chunks: strided pass (one
/// sweep), block-local stages `16 .. 2^15` (one sweep), then the global
/// levels (two radix-16 sweeps or one radix-256 sweep).
pub unsafe fn lde_coset_strided_into(
    part: &[u32],
    chunk_stride: usize,
    log_n: u32,
    offset: BabyBearField,
    tw: &[u32],
    ao: &[u32],
    bo: &[u32],
    out: &mut [u32],
    worker: &Worker,
    cfg: StridedCfg,
) {
    let n = 1usize << log_n;
    check_strided_args(part, chunk_stride, log_n, out, &cfg);
    assert_eq!(
        cfg.blk_log2, 16,
        "the non-gather strided pipeline uses 2^16 blocks"
    );
    let (stream, obs) = (cfg.stream, cfg.out_block_stride);
    let omega = BabyBearField::from_raw_u32(tw[n / 4]);
    let k = StridedConsts::new(omega, offset, log_n);
    let kr = &k;
    let lines = n >> 8;
    let (p_addr, o_addr) = (part.as_ptr() as usize, out.as_mut_ptr() as usize);
    worker.scope(lines, |scope, geometry| {
        let (work, chunks) = (lines, geometry.len());
        for idx in 0..chunks {
            let (start, size) = balanced_chunk(work, chunks, idx);
            spawn_chunk(scope, idx == chunks - 1, move |_| {
                strided_lines_to_out(
                    p_addr as *const u32,
                    chunk_stride,
                    o_addr as *mut u32,
                    log_n,
                    start..start + size,
                    kr,
                    stream,
                    obs,
                );
            });
        }
    });
    block_local_from16_parallel(out, tw, ao, bo, worker, obs);
    if cfg.r256 {
        phase_b_radix256(out, log_n, tw, ao, bo, worker, cfg);
    } else {
        phase_b_global(out, log_n, &tw[..n / 2], ao, bo, worker);
    }
}

/// Gather variant of the strided pass for block group `c` (blocks
/// `c + bpc * s`, `s < 16`, `bpc` = blocks of `2^blk_log2` per chunk): its
/// tiles are the lines `L = rev(c) + bpc * J`, read as 16 strided streams;
/// the 16 output lines of a tile land in the 16 buffered blocks (`s =
/// rev4(l)`, line `rev(J)`, buffer blocks `buf_block_stride` apart), then
/// each block gets its block-local stages while it is cache-resident and is
/// copied out once (block `b` at `b * out_block_stride`).
#[target_feature(enable = "avx512f")]
unsafe fn strided_gather_group(
    part: *const u32,
    chunk_stride: usize,
    out: *mut u32,
    log_n: u32,
    c: usize,
    k: &StridedConsts,
    tw: *const u32,
    ao: *const u32,
    bo: *const u32,
    buf: *mut u32,
    stream: bool,
    out_block_stride: usize,
    blk_log2: u32,
    buf_block_stride: usize,
) {
    let blk = 1usize << blk_log2;
    let bpc_log2 = log_n - 4 - blk_log2;
    let bpc = 1usize << bpc_log2;
    let l0 = rev_bits(c, bpc_log2);
    let tiles_log2 = blk_log2 - 4;
    let tiles = 1usize << tiles_log2;
    let mut regs = StridedRegs::new(k, l0, bpc);
    for j in 0..tiles {
        let rows = strided_tile(part, chunk_stride, l0 + bpc * j, &regs);
        let rj = rev_bits(j, tiles_log2);
        for l in 0..16 {
            st(buf.add(REV4[l] * buf_block_stride + rj * 16), rows[l]);
        }
        regs.advance();
    }
    for s in 0..16 {
        let b = c + bpc * s;
        let p = buf.add(s * buf_block_stride);
        if blk_log2 == 16 {
            ntt_block_local_from16(p, b, tw, ao, bo);
        } else {
            ntt_sub_block_from16(p, b, tw, ao, bo);
        }
        let dst = out.add(b * out_block_stride);
        if stream {
            let mut q = 0usize;
            while q < blk {
                st_nt(dst.add(q), ld(p.add(q)));
                q += 16;
            }
        } else {
            core::ptr::copy_nonoverlapping(p, dst, blk);
        }
    }
    if stream {
        _mm_sfence();
    }
}

/// The gather pass alone (strided pass fused with the block-local stages,
/// one sweep): `out` is left in the DIT layout with levels up to `2^15` done.
pub unsafe fn strided_gather_pass_into(
    part: &[u32],
    chunk_stride: usize,
    log_n: u32,
    offset: BabyBearField,
    tw: &[u32],
    ao: &[u32],
    bo: &[u32],
    out: &mut [u32],
    worker: &Worker,
    cfg: StridedCfg,
) {
    let n = 1usize << log_n;
    check_strided_args(part, chunk_stride, log_n, out, &cfg);
    let (stream, obs) = (cfg.stream, cfg.out_block_stride);
    let omega = BabyBearField::from_raw_u32(tw[n / 4]);
    let k = StridedConsts::new(omega, offset, log_n);
    let kr = &k;
    let (blk_log2, bbs) = (cfg.blk_log2, (1usize << cfg.blk_log2) + 64);
    let groups = 1usize << (log_n - 4 - blk_log2);
    let (p_addr, o_addr) = (part.as_ptr() as usize, out.as_mut_ptr() as usize);
    let (t_addr, ao_addr, bo_addr) = (
        tw.as_ptr() as usize,
        ao.as_ptr() as usize,
        bo.as_ptr() as usize,
    );
    worker.scope(groups, |scope, geometry| {
        let (work, chunks) = (groups, geometry.len());
        for idx in 0..chunks {
            let (start, size) = balanced_chunk(work, chunks, idx);
            spawn_chunk(scope, idx == chunks - 1, move |_| {
                with_group_buf(16 * bbs, |buf| {
                    for c in start..start + size {
                        strided_gather_group(
                            p_addr as *const u32,
                            chunk_stride,
                            o_addr as *mut u32,
                            log_n,
                            c,
                            kr,
                            t_addr as *const u32,
                            ao_addr as *const u32,
                            bo_addr as *const u32,
                            buf as *mut u32,
                            stream,
                            obs,
                            blk_log2,
                            bbs,
                        );
                    }
                });
            });
        }
    });
}

/// Global levels above the block: two radix-16 sweeps or one radix-256 sweep.
pub unsafe fn strided_global_phase(
    out: &mut [u32],
    log_n: u32,
    tw: &[u32],
    ao: &[u32],
    bo: &[u32],
    worker: &Worker,
    cfg: StridedCfg,
) {
    let n = 1usize << log_n;
    if cfg.blk_log2 == 14 {
        phase_b_radix1024(out, log_n, tw, ao, bo, worker, cfg);
    } else if cfg.r256 {
        phase_b_radix256(out, log_n, tw, ao, bo, worker, cfg);
    } else {
        phase_b_global(out, log_n, &tw[..n / 2], ao, bo, worker);
    }
}

/// Coset LDE from the partially transformed chunks with the gather variant:
/// gather pass (one sweep), then the global levels.
pub unsafe fn lde_coset_strided_gather_into(
    part: &[u32],
    chunk_stride: usize,
    log_n: u32,
    offset: BabyBearField,
    tw: &[u32],
    ao: &[u32],
    bo: &[u32],
    out: &mut [u32],
    worker: &Worker,
    cfg: StridedCfg,
) {
    strided_gather_pass_into(
        part,
        chunk_stride,
        log_n,
        offset,
        tw,
        ao,
        bo,
        out,
        worker,
        cfg,
    );
    strided_global_phase(out, log_n, tw, ao, bo, worker, cfg);
}

// ------------------------------------------------------------------------
// L1-blocked radix-256 global pass (8 levels per DRAM sweep)
// ------------------------------------------------------------------------

/// Radix-256 over the 256 blocks (`ppg = 2^16`, `log_n = 24`, block `i` at
/// `i * block_stride`), by groups of `g_items` consecutive lines per stream:
/// the group (`g_items` x 16 KB) is copied in with `g_items` consecutive
/// lines per stream, each of its items gets the two radix-16 passes in L1,
/// and it is written back the same way (non-temporal when `stream`). With
/// `prefetch`, the next group's lines are software-prefetched into L2 during
/// the compute (two streams per radix-16 core) — only useful with a padded
/// `block_stride`, since 256 streams at a power-of-two stride share one set.
#[target_feature(enable = "avx512f")]
pub unsafe fn radix256_groups(
    a: *mut u32,
    block_stride: usize,
    tw: *const u32,
    ao: *const u32,
    bo: *const u32,
    group_range: core::ops::Range<usize>,
    g_items: usize,
    stream: bool,
    prefetch: bool,
) {
    assert!((1..=4).contains(&g_items));
    #[repr(align(64))]
    struct L2Buf([core::mem::MaybeUninit<u32>; 4 * 4096]);
    let mut buf = L2Buf([core::mem::MaybeUninit::uninit(); 4 * 4096]);
    let b = buf.0.as_mut_ptr() as *mut u32;
    let lines_total = 1usize << (BLOCK_LOG2 - 4);
    let twa2: [[__m512i; 6]; 4] = core::array::from_fn(|q| twset(tw, ao, bo, q));
    let twb2 = twset(tw, ao, bo, 0);
    let cores = g_items * 32;
    let streams_per_core = 256usize.div_ceil(cores);
    for grp in group_range {
        let jl0 = grp * g_items;
        for i in 0..256 {
            let src = a.add(i * block_stride + jl0 * 16);
            for g in 0..g_items {
                st(b.add(g * 4096 + i * 16), ld(src.add(g * 16)));
            }
        }
        let do_pf = prefetch && jl0 + 2 * g_items <= lines_total;
        let next = a.add((jl0 + g_items) * 16);
        let mut pf_i = 0usize;
        for g in 0..g_items {
            let p = b.add(g * 4096);
            for pass in 0..2 {
                for q in 0..16 {
                    if do_pf {
                        for _ in 0..streams_per_core {
                            if pf_i < 256 {
                                let sp = next.add(pf_i * block_stride);
                                for gg in 0..g_items {
                                    _mm_prefetch::<{ _MM_HINT_T1 }>(sp.add(gg * 16) as *const i8);
                                }
                                pf_i += 1;
                            }
                        }
                    }
                    if pass == 0 {
                        let twa: [[__m512i; 6]; 4] =
                            core::array::from_fn(|q2| twset(tw, ao, bo, 4 * q + q2));
                        let twb = twset(tw, ao, bo, q);
                        let pq = p.add(q * 256);
                        let mut x: [__m512i; 16] = core::array::from_fn(|i| ld(pq.add(i * 16)));
                        radix16_core(&mut x, &twa, &twb);
                        for i in 0..16 {
                            st(pq.add(i * 16), x[i]);
                        }
                    } else {
                        let pq = p.add(q * 16);
                        let mut x: [__m512i; 16] = core::array::from_fn(|i| ld(pq.add(i * 256)));
                        radix16_core(&mut x, &twa2, &twb2);
                        for i in 0..16 {
                            st(pq.add(i * 256), x[i]);
                        }
                    }
                }
            }
        }
        for i in 0..256 {
            let dst = a.add(i * block_stride + jl0 * 16);
            for g in 0..g_items {
                let v = ld(b.add(g * 4096 + i * 16));
                if stream {
                    st_nt(dst.add(g * 16), v);
                } else {
                    st(dst.add(g * 16), v);
                }
            }
        }
    }
    if stream {
        _mm_sfence();
    }
}

/// Global phase (levels above the 2^16 block) as ONE L1/L2-blocked radix-256
/// sweep; needs exactly 8 levels left, i.e. `log_n == 24`.
pub unsafe fn phase_b_radix256(
    a: &mut [u32],
    log_n: u32,
    tw: &[u32],
    ao: &[u32],
    bo: &[u32],
    worker: &Worker,
    cfg: StridedCfg,
) {
    assert_eq!(
        log_n - BLOCK_LOG2,
        8,
        "radix-256 global pass needs 8 levels above the block"
    );
    assert_eq!(cfg.blk_log2, 16);
    assert_eq!(a.len(), out_len(log_n, 16, cfg.out_block_stride));
    if cfg.stream {
        assert_eq!(
            a.as_ptr() as usize % 64,
            0,
            "streaming stores need a 64-byte aligned array"
        );
    }
    let lines = 1usize << (BLOCK_LOG2 - 4);
    assert!(cfg.group >= 1 && lines % cfg.group == 0);
    let groups = lines / cfg.group;
    let base_addr = a.as_mut_ptr() as usize;
    let (t_addr, ao_addr, bo_addr) = (
        tw.as_ptr() as usize,
        ao.as_ptr() as usize,
        bo.as_ptr() as usize,
    );
    worker.scope(groups, |scope, geometry| {
        let (work, chunks) = (groups, geometry.len());
        for idx in 0..chunks {
            let (start, size) = balanced_chunk(work, chunks, idx);
            spawn_chunk(scope, idx == chunks - 1, move |_| {
                radix256_groups(
                    base_addr as *mut u32,
                    cfg.out_block_stride,
                    t_addr as *const u32,
                    ao_addr as *const u32,
                    bo_addr as *const u32,
                    start..start + size,
                    cfg.group,
                    cfg.stream,
                    cfg.prefetch,
                );
            });
        }
    });
}

/// Separate-prep AVX-512 coset LDE with the radix-256 global phase: prep
/// sweep, all block-local levels, one radix-256 sweep (3 sweeps per coset).
pub unsafe fn lde_coset_avx512_r256_into(
    input: &[u32],
    offset: BabyBearField,
    tw: &[u32],
    ext: &Avx2TwiddleExt,
    out: &mut [u32],
    worker: &Worker,
    stream: bool,
) {
    let n = input.len();
    let log_n = n.trailing_zeros();
    assert!(n >= (1usize << BLOCK_LOG2) && out.len() == n);
    super::baby_bear_avx2::lde_prepare_bitrev_scaled_into(input, out, offset, worker);
    block_local_parallel(out, tw, &ext.ao, &ext.bo, worker, false, 1 << BLOCK_LOG2);
    phase_b_radix256(
        out,
        log_n,
        tw,
        &ext.ao,
        &ext.bo,
        worker,
        StridedCfg {
            stream,
            r256: true,
            out_block_stride: 1 << BLOCK_LOG2,
            group: 1,
            prefetch: false,
            blk_log2: 16,
        },
    );
}

// ------------------------------------------------------------------------
// L2-blocked radix-1024 global pass for 2^14 blocks (10 levels per sweep)
// ------------------------------------------------------------------------

/// Radix-1024 over the 1024 blocks of 2^14 (`log_n = 24`, block `i` at
/// `i * block_stride`): item `jl` = line `jl` of every block, copied into a
/// 64 KB L2 buffer; there: radix-16 over lines `16 q + i` (group `q`, levels
/// 2^14..2^17), radix-16 over lines `i_lo + 16 i_mid + 256 i_top` varying
/// `i_mid` (group `i_top`, levels 2^18..2^21), radix-4 over `i_top` (group
/// 0, levels 2^22, 2^23). Non-temporal write-back when `stream`; with
/// `prefetch`, the next item's lines are prefetched into L2 during the
/// compute (six lines per core call).
#[target_feature(enable = "avx512f")]
pub unsafe fn radix1024_items(
    a: *mut u32,
    block_stride: usize,
    tw: *const u32,
    ao: *const u32,
    bo: *const u32,
    item_range: core::ops::Range<usize>,
    stream: bool,
    prefetch: bool,
) {
    #[repr(align(64))]
    struct L2Buf([core::mem::MaybeUninit<u32>; 16384]);
    let mut buf = L2Buf([core::mem::MaybeUninit::uninit(); 16384]);
    let b = buf.0.as_mut_ptr() as *mut u32;
    let lines_total = 1usize << (14 - 4);
    let tw0 = twset(tw, ao, bo, 0);
    let twa_top: [[[__m512i; 6]; 4]; 4] =
        core::array::from_fn(|t| core::array::from_fn(|q2| twset(tw, ao, bo, 4 * t + q2)));
    let twb_top: [[__m512i; 6]; 4] = core::array::from_fn(|t| twset(tw, ao, bo, t));
    for jl in item_range {
        for i in 0..1024 {
            st(b.add(i * 16), ld(a.add(i * block_stride + jl * 16)));
        }
        let do_pf = prefetch && jl + 1 < lines_total;
        let next = a.add((jl + 1) * 16);
        let mut pf_i = 0usize;
        let mut pf = |pf_i: &mut usize| {
            if do_pf {
                for _ in 0..6 {
                    if *pf_i < 1024 {
                        _mm_prefetch::<{ _MM_HINT_T1 }>(next.add(*pf_i * block_stride) as *const i8);
                        *pf_i += 1;
                    }
                }
            }
        };
        for q in 0..64 {
            pf(&mut pf_i);
            let twa: [[__m512i; 6]; 4] = core::array::from_fn(|q2| twset(tw, ao, bo, 4 * q + q2));
            let twb = twset(tw, ao, bo, q);
            let pq = b.add(q * 256);
            let mut x: [__m512i; 16] = core::array::from_fn(|i| ld(pq.add(i * 16)));
            radix16_core(&mut x, &twa, &twb);
            for i in 0..16 {
                st(pq.add(i * 16), x[i]);
            }
        }
        for g in 0..64 {
            pf(&mut pf_i);
            let (i_lo, i_top) = (g % 16, g / 16);
            let base = b.add((i_lo + 256 * i_top) * 16);
            let mut x: [__m512i; 16] = core::array::from_fn(|m| ld(base.add(m * 256)));
            radix16_core(&mut x, &twa_top[i_top], &twb_top[i_top]);
            for m in 0..16 {
                st(base.add(m * 256), x[m]);
            }
        }
        for g in 0..64 {
            pf(&mut pf_i);
            for r in 4 * g..4 * g + 4 {
                let base = b.add(r * 16);
                let [s_a, s_b, s_o, s_ao, s_bo, bias] = tw0;
                let (z0, z1, z2, z3) = fwd_core(
                    ld(base),
                    ld(base.add(4096)),
                    ld(base.add(8192)),
                    ld(base.add(12288)),
                    s_a,
                    s_b,
                    s_o,
                    s_ao,
                    s_bo,
                    bias,
                );
                st(base, z0);
                st(base.add(4096), z1);
                st(base.add(8192), z2);
                st(base.add(12288), z3);
            }
        }
        for i in 0..1024 {
            let v = ld(b.add(i * 16));
            let dst = a.add(i * block_stride + jl * 16);
            if stream {
                st_nt(dst, v);
            } else {
                st(dst, v);
            }
        }
    }
    if stream {
        _mm_sfence();
    }
}

/// Global phase for 2^14 blocks as ONE L2-blocked radix-1024 sweep
/// (`log_n == 24`).
pub unsafe fn phase_b_radix1024(
    a: &mut [u32],
    log_n: u32,
    tw: &[u32],
    ao: &[u32],
    bo: &[u32],
    worker: &Worker,
    cfg: StridedCfg,
) {
    assert_eq!(
        log_n, 24,
        "radix-1024 global pass needs 10 levels above the 2^14 block"
    );
    assert_eq!(cfg.blk_log2, 14);
    assert_eq!(a.len(), out_len(log_n, 14, cfg.out_block_stride));
    if cfg.stream {
        assert_eq!(
            a.as_ptr() as usize % 64,
            0,
            "streaming stores need a 64-byte aligned array"
        );
    }
    let items = 1usize << (14 - 4);
    let base_addr = a.as_mut_ptr() as usize;
    let (t_addr, ao_addr, bo_addr) = (
        tw.as_ptr() as usize,
        ao.as_ptr() as usize,
        bo.as_ptr() as usize,
    );
    worker.scope(items, |scope, geometry| {
        let (work, chunks) = (items, geometry.len());
        for idx in 0..chunks {
            let (start, size) = balanced_chunk(work, chunks, idx);
            spawn_chunk(scope, idx == chunks - 1, move |_| {
                radix1024_items(
                    base_addr as *mut u32,
                    cfg.out_block_stride,
                    t_addr as *const u32,
                    ao_addr as *const u32,
                    bo_addr as *const u32,
                    start..start + size,
                    cfg.stream,
                    cfg.prefetch,
                );
            });
        }
    });
}
