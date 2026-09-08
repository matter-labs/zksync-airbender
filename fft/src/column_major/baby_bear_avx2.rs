//! AVX2-vectorized BabyBear LDE-coset kernels (x86-64) — the twin of
//! `baby_bear_neon` for the BabyBear work-stealing backend on AVX2 hosts.
//!
//! BabyBear is `p = 2^31 - 2^27 + 1` in standard 32-bit Montgomery form
//! (`R = 2^32`), canonical at rest: EIGHT elements per 256-bit vector, the
//! Montgomery product via even/odd `vpmuludq` pairs + a `vpblendd` high-word
//! merge + one `vpminud` conditional subtract. Every op returns canonical
//! values, so every kernel is BYTE-IDENTICAL to its scalar reference
//! (asserted by the tests).
//!
//! Stage plan of the GS DIT NTT (bit-reversed input → natural output):
//! `ppg == 1`, `2` and `4` run as in-register shuffle passes (cross-lane
//! `vpermd` / `vpermq` / `vperm2i128` de-interleaves, `vpunpck*` re-
//! interleaves); `ppg >= 8` stages run as radix-4 FUSED passes with u64
//! accumulation on the odd outputs (two butterfly levels per sweep, the same
//! combined-twiddle tables as the NEON kernel); the last multiplying level is
//! fused with the final twiddle-free level.
//!
//! The Ext4 kernels hold TWO extension elements per vector (one element =
//! four base coefficients = one 128-bit half); every butterfly is component-
//! wise, so items are processed in contiguous pairs, and the only special
//! case is the stage whose two paired elements belong to different butterfly
//! groups (`ppg == 1` / `half_d == 1` / `s == 1`), handled by a 128-bit-half
//! regrouping through `vperm2i128`. Odd item counts fall back to a single
//! element in the low half of the vector.

#![cfg(all(target_arch = "x86_64", target_feature = "avx2"))]

use field::baby_bear::base::BabyBearField;
use field::Field;

pub const P: u32 = 0x78000001;
pub const K: u32 = 0x77ffffff;

#[inline(always)]
fn mont_mul_scalar(a: u32, b: u32) -> u32 {
    let mut product = (a as u64).wrapping_mul(b as u64);
    let m = (product as u32).wrapping_mul(K);
    product = product.wrapping_add((m as u64).wrapping_mul(P as u64));
    let mut result = (product >> 32) as u32;
    if result >= P {
        result -= P;
    }
    result
}

/// Split-table offset powers on RAW values: `f_i = lo[i & mask] * hi[i >> h]`,
/// exactly as `lde_coset_natural_seq_fused` computes them (same op order =>
/// identical canonical values).
struct SplitPowersRaw {
    lo: Vec<u32>,
    hi: Vec<u32>,
    h: u32,
    mask: usize,
}

impl SplitPowersRaw {
    fn new(offset: BabyBearField, log_n: u32) -> Self {
        let h = log_n.div_ceil(2);
        let lo_len = 1usize << h;
        let hi_len = 1usize << (log_n - h);
        let mut lo = Vec::with_capacity(lo_len);
        let mut cur = BabyBearField::ONE;
        for _ in 0..lo_len {
            lo.push(cur.raw_u32_value());
            cur.mul_assign(&offset);
        }
        let stride = cur;
        let mut hi = Vec::with_capacity(hi_len);
        let mut cur = BabyBearField::ONE;
        for _ in 0..hi_len {
            hi.push(cur.raw_u32_value());
            cur.mul_assign(&stride);
        }
        Self {
            lo,
            hi,
            h,
            mask: lo_len - 1,
        }
    }
}

/// 8-lane canonical Montgomery arithmetic + the shared radix-4 butterfly
/// cores (used by both the base-field and the Ext4 kernels).

/// Chunk spawner for the worker-parallel kernels of this module.
/// `Worker::smart_spawn` runs the last chunk inline on the CALLING thread;
/// when the caller is not a pool worker and every CPU is already occupied by
/// pool workers (a 96-thread pool on a 96-core socket driven from the main
/// thread), that chunk is time-sliced against them — measured 7.6 ms for a
/// 0.3 ms chunk, i.e. the whole phase waits on it. So the last chunk runs
/// inline only when the caller is itself a pool worker; from any other
/// thread every chunk is spawned and the caller just waits.
#[inline(always)]
pub fn spawn_chunk<'scope, BODY>(scope: &worker::rayon::Scope<'scope>, is_last: bool, body: BODY)
where
    BODY: FnOnce(&worker::rayon::Scope<'scope>) + Send + 'scope,
{
    if is_last && worker::rayon::current_thread_index().is_some() {
        body(scope);
    } else {
        scope.spawn(body);
    }
}

/// Balanced chunk `t` of `work` items over `chunks` chunks: sizes differ by
/// at most one. The worker geometry instead gives the last chunk
/// `work - (chunks-1)*floor(work/chunks)` — 66 vs 2 blocks for 256 blocks on
/// 96 threads — so a block phase waited on one 33x chunk (measured 8 ms vs
/// 0.8 ms at 64 threads). Used by every scope of the x86 kernels.
#[inline(always)]
pub fn balanced_chunk(work: usize, chunks: usize, t: usize) -> (usize, usize) {
    let q = work / chunks;
    let r = work % chunks;
    (t * q + t.min(r), q + (t < r) as usize)
}

pub mod avx2 {
    use super::{balanced_chunk, spawn_chunk, SplitPowersRaw, K, P};
    use core::arch::x86_64::*;
    use worker::Worker;

    #[inline(always)]
    pub unsafe fn pv() -> __m256i {
        _mm256_set1_epi32(P as i32)
    }

    #[inline(always)]
    unsafe fn kv() -> __m256i {
        _mm256_set1_epi32(K as i32)
    }

    /// Canonical Montgomery product on 8 lanes: `a*b + m*p` in 64-bit even/odd
    /// lanes, high words merged, one conditional subtract.
    #[inline(always)]
    pub unsafe fn mont_mul(a: __m256i, b: __m256i) -> __m256i {
        let lo = _mm256_mullo_epi32(a, b);
        let m = _mm256_mullo_epi32(lo, kv());
        let prod_e = _mm256_mul_epu32(a, b);
        let prod_o = _mm256_mul_epu32(_mm256_srli_epi64::<32>(a), _mm256_srli_epi64::<32>(b));
        let mp_e = _mm256_mul_epu32(m, pv());
        let mp_o = _mm256_mul_epu32(_mm256_srli_epi64::<32>(m), pv());
        let t_e = _mm256_add_epi64(prod_e, mp_e);
        let t_o = _mm256_add_epi64(prod_o, mp_o);
        // even results: high dword of t_e shifted down; odd results: high
        // dword of t_o already sits in the odd position
        let r = _mm256_blend_epi32::<0b1010_1010>(_mm256_srli_epi64::<32>(t_e), t_o);
        let rs = _mm256_sub_epi32(r, pv());
        _mm256_min_epu32(r, rs)
    }

    #[inline(always)]
    pub unsafe fn add(a: __m256i, b: __m256i) -> __m256i {
        let s = _mm256_add_epi32(a, b);
        _mm256_min_epu32(s, _mm256_sub_epi32(s, pv()))
    }

    #[inline(always)]
    pub unsafe fn sub(a: __m256i, b: __m256i) -> __m256i {
        let d = _mm256_sub_epi32(a, b);
        _mm256_min_epu32(d, _mm256_add_epi32(d, pv()))
    }

    #[inline(always)]
    pub unsafe fn butterfly(u: __m256i, v: __m256i, s: __m256i) -> (__m256i, __m256i) {
        (add(u, v), mont_mul(sub(u, v), s))
    }

    /// Montgomery REDC of 64-bit lane accumulators (`t < R*p`): `t_e` holds
    /// the even elements' accumulators (64-bit lanes), `t_o` the odd ones.
    /// Canonical out.
    #[inline(always)]
    pub unsafe fn redc64(t_e: __m256i, t_o: __m256i) -> __m256i {
        let m_e = _mm256_mullo_epi32(t_e, kv());
        let m_o = _mm256_mullo_epi32(t_o, kv());
        let s_e = _mm256_add_epi64(t_e, _mm256_mul_epu32(m_e, pv()));
        let s_o = _mm256_add_epi64(t_o, _mm256_mul_epu32(m_o, pv()));
        let r = _mm256_blend_epi32::<0b1010_1010>(_mm256_srli_epi64::<32>(s_e), s_o);
        let rs = _mm256_sub_epi32(r, pv());
        _mm256_min_epu32(r, rs)
    }

    /// 32x32 -> 64 products of the even lanes and of the odd lanes.
    #[inline(always)]
    pub unsafe fn widening_mul(a: __m256i, b: __m256i) -> (__m256i, __m256i) {
        (
            _mm256_mul_epu32(a, b),
            _mm256_mul_epu32(_mm256_srli_epi64::<32>(a), _mm256_srli_epi64::<32>(b)),
        )
    }

    /// FORWARD (GS) radix-4 fused butterfly with u64 accumulation on the odd
    /// outputs: `z1 = REDC(d01*s_a + d23*s_b)`, `z3 = REDC(d01*s_ao -
    /// d23*s_bo + p*s_bo)` with the combined twiddles `s_ao = mont(tw[2k],
    /// tw[k])`, `s_bo = mont(tw[2k+1], tw[k])`. `bias` is `p * s_bo` as four
    /// u64 lanes. Accumulators < 2p^2 < R*p, so REDC stays exact.
    #[inline(always)]
    pub unsafe fn fwd_core(
        x0: __m256i,
        x1: __m256i,
        x2: __m256i,
        x3: __m256i,
        s_a: __m256i,
        s_b: __m256i,
        s_o: __m256i,
        s_ao: __m256i,
        s_bo: __m256i,
        bias: __m256i,
    ) -> (__m256i, __m256i, __m256i, __m256i) {
        let y0 = add(x0, x1);
        let y2 = add(x2, x3);
        let z0 = add(y0, y2);
        let z2 = mont_mul(sub(y0, y2), s_o);

        let d01 = sub(x0, x1);
        let d23 = sub(x2, x3);
        let (p1e, p1o) = widening_mul(d01, s_a);
        let (p2e, p2o) = widening_mul(d23, s_b);
        let z1 = redc64(_mm256_add_epi64(p1e, p2e), _mm256_add_epi64(p1o, p2o));
        let (p3e, p3o) = widening_mul(d01, s_ao);
        let (p4e, p4o) = widening_mul(d23, s_bo);
        let z3 = redc64(
            _mm256_sub_epi64(_mm256_add_epi64(p3e, bias), p4e),
            _mm256_sub_epi64(_mm256_add_epi64(p3o, bias), p4o),
        );
        (z0, z1, z2, z3)
    }

    /// INVERSE (CT) radix-4 fused butterfly with u64 accumulation (the same
    /// combined tables serve since `mont` commutes):
    /// `m1 = REDC(x1*s_a + x3*ao)` (= `(x1 + x3*s)*s_a`),
    /// `m2 = REDC(x1*s_b - x3*bo + p*bo)` (= `(x1 - x3*s)*s_b`), `t2 = x2*s`.
    #[inline(always)]
    pub unsafe fn inv_core(
        x0: __m256i,
        x1: __m256i,
        x2: __m256i,
        x3: __m256i,
        s: __m256i,
        s_a: __m256i,
        s_b: __m256i,
        s_ao: __m256i,
        s_bo: __m256i,
        bias: __m256i,
    ) -> (__m256i, __m256i, __m256i, __m256i) {
        let t2 = mont_mul(x2, s);
        let y0 = add(x0, t2);
        let y2 = sub(x0, t2);

        let (p1e, p1o) = widening_mul(x1, s_a);
        let (p2e, p2o) = widening_mul(x3, s_ao);
        let m1 = redc64(_mm256_add_epi64(p1e, p2e), _mm256_add_epi64(p1o, p2o));
        let (p3e, p3o) = widening_mul(x1, s_b);
        let (p4e, p4o) = widening_mul(x3, s_bo);
        let m2 = redc64(
            _mm256_sub_epi64(_mm256_add_epi64(p3e, bias), p4e),
            _mm256_sub_epi64(_mm256_add_epi64(p3o, bias), p4o),
        );
        (add(y0, m1), sub(y0, m1), add(y2, m2), sub(y2, m2))
    }

    /// `p * bo` broadcast to all four u64 lanes.
    #[inline(always)]
    pub unsafe fn bias_all(bo: u32) -> __m256i {
        _mm256_set1_epi64x(((P as u64) * (bo as u64)) as i64)
    }

    // ---------------------------------------------------------------- base field

    /// `ppg == 1`: element pairs `(2k, 2k+1)`, twiddle `tw[k]`; 16 elements
    /// per iteration, cross-lane de-interleave / re-interleave.
    #[inline(always)]
    unsafe fn pass_ppg1(a: *mut u32, n: usize, tw: *const u32) {
        let idx = _mm256_setr_epi32(0, 2, 4, 6, 1, 3, 5, 7);
        let mut j = 0usize;
        while j < n {
            let v0 = _mm256_loadu_si256(a.add(j) as *const __m256i);
            let v1 = _mm256_loadu_si256(a.add(j + 8) as *const __m256i);
            let p0 = _mm256_permutevar8x32_epi32(v0, idx);
            let p1 = _mm256_permutevar8x32_epi32(v1, idx);
            let u = _mm256_permute2x128_si256::<0x20>(p0, p1);
            let v = _mm256_permute2x128_si256::<0x31>(p0, p1);
            let s = _mm256_loadu_si256(tw.add(j >> 1) as *const __m256i);
            let (na, nb) = butterfly(u, v, s);
            let lo = _mm256_unpacklo_epi32(na, nb);
            let hi = _mm256_unpackhi_epi32(na, nb);
            _mm256_storeu_si256(
                a.add(j) as *mut __m256i,
                _mm256_permute2x128_si256::<0x20>(lo, hi),
            );
            _mm256_storeu_si256(
                a.add(j + 8) as *mut __m256i,
                _mm256_permute2x128_si256::<0x31>(lo, hi),
            );
            j += 16;
        }
    }

    /// `ppg == 2`: 64-bit units `(u, v)` per group of 4, twiddle `tw[k]`
    /// duplicated over the unit; 16 elements per iteration.
    #[inline(always)]
    unsafe fn pass_ppg2(a: *mut u32, n: usize, tw: *const u32) {
        let dup = _mm256_setr_epi32(0, 0, 1, 1, 2, 2, 3, 3);
        let mut j = 0usize;
        while j < n {
            let v0 = _mm256_loadu_si256(a.add(j) as *const __m256i);
            let v1 = _mm256_loadu_si256(a.add(j + 8) as *const __m256i);
            // [q0 q2 | q1 q3] = [u(g0) u(g1) | v(g0) v(g1)]
            let p0 = _mm256_permute4x64_epi64::<0xD8>(v0);
            let p1 = _mm256_permute4x64_epi64::<0xD8>(v1);
            let u = _mm256_permute2x128_si256::<0x20>(p0, p1);
            let v = _mm256_permute2x128_si256::<0x31>(p0, p1);
            let t4 = _mm_loadu_si128(tw.add(j >> 2) as *const __m128i);
            let s = _mm256_permutevar8x32_epi32(_mm256_zextsi128_si256(t4), dup);
            let (na, nb) = butterfly(u, v, s);
            let lo = _mm256_unpacklo_epi64(na, nb);
            let hi = _mm256_unpackhi_epi64(na, nb);
            _mm256_storeu_si256(
                a.add(j) as *mut __m256i,
                _mm256_permute2x128_si256::<0x20>(lo, hi),
            );
            _mm256_storeu_si256(
                a.add(j + 8) as *mut __m256i,
                _mm256_permute2x128_si256::<0x31>(lo, hi),
            );
            j += 16;
        }
    }

    /// `ppg == 4`: 128-bit units per group of 8, twiddle `tw[k]` broadcast
    /// over the half; 16 elements per iteration.
    #[inline(always)]
    unsafe fn pass_ppg4(a: *mut u32, n: usize, tw: *const u32) {
        let mut j = 0usize;
        while j < n {
            let v0 = _mm256_loadu_si256(a.add(j) as *const __m256i);
            let v1 = _mm256_loadu_si256(a.add(j + 8) as *const __m256i);
            let u = _mm256_permute2x128_si256::<0x20>(v0, v1);
            let v = _mm256_permute2x128_si256::<0x31>(v0, v1);
            let k = j >> 3;
            let s = _mm256_set_m128i(
                _mm_set1_epi32(*tw.add(k + 1) as i32),
                _mm_set1_epi32(*tw.add(k) as i32),
            );
            let (na, nb) = butterfly(u, v, s);
            _mm256_storeu_si256(
                a.add(j) as *mut __m256i,
                _mm256_permute2x128_si256::<0x20>(na, nb),
            );
            _mm256_storeu_si256(
                a.add(j + 8) as *mut __m256i,
                _mm256_permute2x128_si256::<0x31>(na, nb),
            );
            j += 16;
        }
    }

    /// Radix-4 fused pass for `ppg >= 8`: two levels per sweep, broadcast
    /// twiddles, u64 accumulation on the odd outputs.
    #[inline(always)]
    unsafe fn radix4_pass_acc(
        a: *mut u32,
        ppg: usize,
        num_groups: usize,
        tw: *const u32,
        tw_ao: *const u32,
        tw_bo: *const u32,
    ) {
        let ng_outer = num_groups / 2;
        for k2 in 0..ng_outer {
            let s_a = _mm256_set1_epi32(*tw.add(2 * k2) as i32);
            let s_b = _mm256_set1_epi32(*tw.add(2 * k2 + 1) as i32);
            let s_o = _mm256_set1_epi32(*tw.add(k2) as i32);
            let s_ao = _mm256_set1_epi32(*tw_ao.add(k2) as i32);
            let s_bo = _mm256_set1_epi32(*tw_bo.add(k2) as i32);
            let bias = bias_all(*tw_bo.add(k2));
            let base = k2 * ppg * 4;
            let mut j = base;
            while j < base + ppg {
                let x0 = _mm256_loadu_si256(a.add(j) as *const __m256i);
                let x1 = _mm256_loadu_si256(a.add(j + ppg) as *const __m256i);
                let x2 = _mm256_loadu_si256(a.add(j + 2 * ppg) as *const __m256i);
                let x3 = _mm256_loadu_si256(a.add(j + 3 * ppg) as *const __m256i);
                let (z0, z1, z2, z3) = fwd_core(x0, x1, x2, x3, s_a, s_b, s_o, s_ao, s_bo, bias);
                _mm256_storeu_si256(a.add(j) as *mut __m256i, z0);
                _mm256_storeu_si256(a.add(j + ppg) as *mut __m256i, z1);
                _mm256_storeu_si256(a.add(j + 2 * ppg) as *mut __m256i, z2);
                _mm256_storeu_si256(a.add(j + 3 * ppg) as *mut __m256i, z3);
                j += 8;
            }
        }
    }

    #[inline(always)]
    unsafe fn tail_two_groups(a: *mut u32, n: usize, tw: *const u32) {
        let q = n / 4;
        let s_a = _mm256_set1_epi32(*tw as i32);
        let s_b = _mm256_set1_epi32(*tw.add(1) as i32);
        let mut j = 0usize;
        while j < q {
            let x0 = _mm256_loadu_si256(a.add(j) as *const __m256i);
            let x1 = _mm256_loadu_si256(a.add(j + q) as *const __m256i);
            let x2 = _mm256_loadu_si256(a.add(j + 2 * q) as *const __m256i);
            let x3 = _mm256_loadu_si256(a.add(j + 3 * q) as *const __m256i);
            let (y0, y1) = butterfly(x0, x1, s_a);
            let (y2, y3) = butterfly(x2, x3, s_b);
            _mm256_storeu_si256(a.add(j) as *mut __m256i, add(y0, y2));
            _mm256_storeu_si256(a.add(j + 2 * q) as *mut __m256i, sub(y0, y2));
            _mm256_storeu_si256(a.add(j + q) as *mut __m256i, add(y1, y3));
            _mm256_storeu_si256(a.add(j + 3 * q) as *mut __m256i, sub(y1, y3));
            j += 8;
        }
    }

    #[inline(always)]
    unsafe fn tail_final(a: *mut u32, n: usize) {
        let half = n / 2;
        let mut j = 0usize;
        while j < half {
            let u = _mm256_loadu_si256(a.add(j) as *const __m256i);
            let v = _mm256_loadu_si256(a.add(j + half) as *const __m256i);
            _mm256_storeu_si256(a.add(j) as *mut __m256i, add(u, v));
            _mm256_storeu_si256(a.add(j + half) as *mut __m256i, sub(u, v));
            j += 8;
        }
    }

    /// Radix-4 fused pass over VECTOR items `(k2, j8)`: item `t` is the outer
    /// group `k2 = t / (ppg/8)` — twiddle index `k2 + k2_offset` — and the
    /// vector `j8 = t % (ppg/8)` within it. `ppg >= 8`. Twiddles are loaded
    /// once per run of consecutive vectors of one group.
    #[inline(always)]
    pub unsafe fn radix4_items(
        a: *mut u32,
        ppg: usize,
        tw: *const u32,
        tw_ao: *const u32,
        tw_bo: *const u32,
        k2_offset: usize,
        item_range: core::ops::Range<usize>,
    ) {
        let vecs_per_group = ppg / 8;
        let mut t = item_range.start;
        while t < item_range.end {
            let k2 = t / vecs_per_group;
            let j8 = t % vecs_per_group;
            let kg = k2 + k2_offset;
            let s_a = _mm256_set1_epi32(*tw.add(2 * kg) as i32);
            let s_b = _mm256_set1_epi32(*tw.add(2 * kg + 1) as i32);
            let s_o = _mm256_set1_epi32(*tw.add(kg) as i32);
            let s_ao = _mm256_set1_epi32(*tw_ao.add(kg) as i32);
            let s_bo = _mm256_set1_epi32(*tw_bo.add(kg) as i32);
            let bias = bias_all(*tw_bo.add(kg));
            let run = (vecs_per_group - j8).min(item_range.end - t);
            let mut j = k2 * ppg * 4 + j8 * 8;
            for _ in 0..run {
                let x0 = _mm256_loadu_si256(a.add(j) as *const __m256i);
                let x1 = _mm256_loadu_si256(a.add(j + ppg) as *const __m256i);
                let x2 = _mm256_loadu_si256(a.add(j + 2 * ppg) as *const __m256i);
                let x3 = _mm256_loadu_si256(a.add(j + 3 * ppg) as *const __m256i);
                let (z0, z1, z2, z3) = fwd_core(x0, x1, x2, x3, s_a, s_b, s_o, s_ao, s_bo, bias);
                _mm256_storeu_si256(a.add(j) as *mut __m256i, z0);
                _mm256_storeu_si256(a.add(j + ppg) as *mut __m256i, z1);
                _mm256_storeu_si256(a.add(j + 2 * ppg) as *mut __m256i, z2);
                _mm256_storeu_si256(a.add(j + 3 * ppg) as *mut __m256i, z3);
                j += 8;
            }
            t += run;
        }
    }

    /// Single-level (radix-2) pass over VECTOR items `(k, j8)`: group `k`
    /// (twiddle index `k + k_offset`) of size `2*ppg`. `ppg >= 8`.
    #[inline(always)]
    pub unsafe fn radix2_items(
        a: *mut u32,
        ppg: usize,
        tw: *const u32,
        k_offset: usize,
        item_range: core::ops::Range<usize>,
    ) {
        let vecs_per_group = ppg / 8;
        let mut t = item_range.start;
        while t < item_range.end {
            let k = t / vecs_per_group;
            let j8 = t % vecs_per_group;
            let s = _mm256_set1_epi32(*tw.add(k + k_offset) as i32);
            let run = (vecs_per_group - j8).min(item_range.end - t);
            let mut j = k * ppg * 2 + j8 * 8;
            for _ in 0..run {
                let u = _mm256_loadu_si256(a.add(j) as *const __m256i);
                let v = _mm256_loadu_si256(a.add(j + ppg) as *const __m256i);
                let (nu, nv) = butterfly(u, v, s);
                _mm256_storeu_si256(a.add(j) as *mut __m256i, nu);
                _mm256_storeu_si256(a.add(j + ppg) as *mut __m256i, nv);
                j += 8;
            }
            t += run;
        }
    }

    /// One radix-16 butterfly network on 16 vectors: the 4 quads of
    /// consecutive positions at levels `(ppg, 2ppg)` (twiddle sets `twa[q]`),
    /// then the 4 quads across the quads at levels `(4ppg, 8ppg)` (`twb`),
    /// each through the u64-accumulation core.
    #[inline(always)]
    pub unsafe fn radix16_core(x: &mut [__m256i; 16], twa: &[[__m256i; 6]; 4], twb: &[__m256i; 6]) {
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

    /// Radix-16 fused pass — FOUR levels `(ppg, 2ppg, 4ppg, 8ppg)` per
    /// load/store sweep — over items `(k4, jl)`: item `t` is the 16ppg-group
    /// `k4 = t / (ppg/16)` (index `k4 + k4_offset` in the level-8ppg twiddle
    /// table) and the 64-byte LINE `jl` (two vectors) within it; `ppg >= 16`.
    /// Two in-register radix-4 stages ([`radix16_core`]). LINE-COMPLETE on
    /// purpose: the 16 streams of a group sit at power-of-two strides and
    /// alias in the same L1/L2 sets, so a line's two vectors must both be
    /// consumed while it is resident. Identical values to two radix-4
    /// passes.
    #[inline(always)]
    pub unsafe fn radix16_items(
        a: *mut u32,
        ppg: usize,
        tw: *const u32,
        tw_ao: *const u32,
        tw_bo: *const u32,
        k4_offset: usize,
        item_range: core::ops::Range<usize>,
    ) {
        debug_assert!(ppg >= 16);
        let lines_per_group = ppg / 16;
        let mut t = item_range.start;
        while t < item_range.end {
            let k4 = t / lines_per_group;
            let jl = t % lines_per_group;
            let kg = k4 + k4_offset;
            let twq = |k2: usize| -> [__m256i; 6] {
                [
                    _mm256_set1_epi32(*tw.add(2 * k2) as i32),
                    _mm256_set1_epi32(*tw.add(2 * k2 + 1) as i32),
                    _mm256_set1_epi32(*tw.add(k2) as i32),
                    _mm256_set1_epi32(*tw_ao.add(k2) as i32),
                    _mm256_set1_epi32(*tw_bo.add(k2) as i32),
                    bias_all(*tw_bo.add(k2)),
                ]
            };
            let twa: [[__m256i; 6]; 4] = core::array::from_fn(|q| twq(4 * kg + q));
            let twb = twq(kg);
            let run = (lines_per_group - jl).min(item_range.end - t);
            let mut j = k4 * ppg * 16 + jl * 16;
            for _ in 0..run {
                let mut x0: [__m256i; 16] = core::array::from_fn(|i| {
                    _mm256_loadu_si256(a.add(j + i * ppg) as *const __m256i)
                });
                let mut x1: [__m256i; 16] = core::array::from_fn(|i| {
                    _mm256_loadu_si256(a.add(j + 8 + i * ppg) as *const __m256i)
                });
                radix16_core(&mut x0, &twa, &twb);
                radix16_core(&mut x1, &twa, &twb);
                for i in 0..16 {
                    _mm256_storeu_si256(a.add(j + i * ppg) as *mut __m256i, x0[i]);
                    _mm256_storeu_si256(a.add(j + 8 + i * ppg) as *mut __m256i, x1[i]);
                }
                j += 16;
            }
            t += run;
        }
    }

    #[inline(always)]
    unsafe fn tail_two_groups_items(
        a: *mut u32,
        n: usize,
        tw: *const u32,
        j8_range: core::ops::Range<usize>,
    ) {
        let q = n / 4;
        let s_a = _mm256_set1_epi32(*tw as i32);
        let s_b = _mm256_set1_epi32(*tw.add(1) as i32);
        for j8 in j8_range {
            let j = j8 * 8;
            let x0 = _mm256_loadu_si256(a.add(j) as *const __m256i);
            let x1 = _mm256_loadu_si256(a.add(j + q) as *const __m256i);
            let x2 = _mm256_loadu_si256(a.add(j + 2 * q) as *const __m256i);
            let x3 = _mm256_loadu_si256(a.add(j + 3 * q) as *const __m256i);
            let (y0, y1) = butterfly(x0, x1, s_a);
            let (y2, y3) = butterfly(x2, x3, s_b);
            _mm256_storeu_si256(a.add(j) as *mut __m256i, add(y0, y2));
            _mm256_storeu_si256(a.add(j + 2 * q) as *mut __m256i, sub(y0, y2));
            _mm256_storeu_si256(a.add(j + q) as *mut __m256i, add(y1, y3));
            _mm256_storeu_si256(a.add(j + 3 * q) as *mut __m256i, sub(y1, y3));
        }
    }

    #[inline(always)]
    unsafe fn tail_final_items(a: *mut u32, n: usize, j8_range: core::ops::Range<usize>) {
        let half = n / 2;
        for j8 in j8_range {
            let j = j8 * 8;
            let u = _mm256_loadu_si256(a.add(j) as *const __m256i);
            let v = _mm256_loadu_si256(a.add(j + half) as *const __m256i);
            _mm256_storeu_si256(a.add(j) as *mut __m256i, add(u, v));
            _mm256_storeu_si256(a.add(j + half) as *mut __m256i, sub(u, v));
        }
    }

    /// In-register 8x8 transpose of eight vectors of eight `u32`s.
    #[inline(always)]
    pub unsafe fn transpose_8x8(r: &mut [__m256i; 8]) {
        let t0 = _mm256_unpacklo_epi32(r[0], r[1]);
        let t1 = _mm256_unpackhi_epi32(r[0], r[1]);
        let t2 = _mm256_unpacklo_epi32(r[2], r[3]);
        let t3 = _mm256_unpackhi_epi32(r[2], r[3]);
        let t4 = _mm256_unpacklo_epi32(r[4], r[5]);
        let t5 = _mm256_unpackhi_epi32(r[4], r[5]);
        let t6 = _mm256_unpacklo_epi32(r[6], r[7]);
        let t7 = _mm256_unpackhi_epi32(r[6], r[7]);
        let u0 = _mm256_unpacklo_epi64(t0, t2);
        let u1 = _mm256_unpackhi_epi64(t0, t2);
        let u2 = _mm256_unpacklo_epi64(t1, t3);
        let u3 = _mm256_unpackhi_epi64(t1, t3);
        let u4 = _mm256_unpacklo_epi64(t4, t6);
        let u5 = _mm256_unpackhi_epi64(t4, t6);
        let u6 = _mm256_unpacklo_epi64(t5, t7);
        let u7 = _mm256_unpackhi_epi64(t5, t7);
        r[0] = _mm256_permute2x128_si256(u0, u4, 0x20);
        r[1] = _mm256_permute2x128_si256(u1, u5, 0x20);
        r[2] = _mm256_permute2x128_si256(u2, u6, 0x20);
        r[3] = _mm256_permute2x128_si256(u3, u7, 0x20);
        r[4] = _mm256_permute2x128_si256(u0, u4, 0x31);
        r[5] = _mm256_permute2x128_si256(u1, u5, 0x31);
        r[6] = _mm256_permute2x128_si256(u2, u6, 0x31);
        r[7] = _mm256_permute2x128_si256(u3, u7, 0x31);
    }

    /// 4-bit reversal of `l < 16`.
    const REV4: [usize; 16] = [0, 8, 4, 12, 2, 10, 6, 14, 1, 9, 5, 13, 3, 11, 7, 15];

    /// Fused "scale by the coset powers + bit-reverse + copy" sweep, out of
    /// place: `dst[rev(k)] = src[k] * pow(k)` (`pow` from the split tables,
    /// `None` = no scaling). Tile structure: for `k = g*16 + l`,
    /// `rev(k) = rev4(l) << c | rev_c(g)` with `c = log_n - 4`, so a batch of
    /// 16 consecutive DESTINATION positions `i0..i0+16` (`g = rev_c(i)`)
    /// reads 16 full 64-byte source lines (random, never a partial line),
    /// scales them, transposes them in registers (four 8x8 transposes) and
    /// writes 16 full destination lines — one streaming read and one
    /// streaming write of the array instead of the copy sweep plus the
    /// in-place bit-reversal sweep. Batches are whole lines on both sides on
    /// purpose (the 16 destination streams alias in the same cache sets).
    /// `n >= 2^8`; batches are chunked over the worker.
    pub(super) unsafe fn scaled_bitrev_copy_parallel(
        src: &[u32],
        dst: &mut [u32],
        sp: Option<&SplitPowersRaw>,
        worker: &Worker,
    ) {
        let n = src.len();
        debug_assert_eq!(dst.len(), n);
        debug_assert!(n >= 256 && n.is_power_of_two());
        let log_n = n.trailing_zeros();
        let c = log_n - 4;
        let stride = 1usize << c;
        let src_addr = src.as_ptr() as usize;
        let dst_addr = dst.as_mut_ptr() as usize;
        let batches = stride / 16;
        worker.scope(batches, |scope, geometry| {
            let (work, chunks) = (batches, geometry.len());
            for thread_idx in 0..chunks {
                let (start, size) = balanced_chunk(work, chunks, thread_idx);
                spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| {
                    let src = src_addr as *const u32;
                    let dst = dst_addr as *mut u32;
                    // [row half][column half]: rows 0..8 / 8..16, lanes 0..8 / 8..16
                    let mut tiles = [[[_mm256_setzero_si256(); 8]; 2]; 2];
                    for batch in start..start + size {
                        let i0 = batch * 16;
                        for b in 0..16 {
                            let g = ((i0 + b) as u32).reverse_bits() >> (32 - c);
                            let k0 = (g as usize) * 16;
                            let mut lo_v = _mm256_loadu_si256(src.add(k0) as *const __m256i);
                            let mut hi_v = _mm256_loadu_si256(src.add(k0 + 8) as *const __m256i);
                            if let Some(sp) = sp {
                                let hi = _mm256_set1_epi32(sp.hi[k0 >> sp.h] as i32);
                                let p_lo = _mm256_loadu_si256(
                                    sp.lo.as_ptr().add(k0 & sp.mask) as *const __m256i
                                );
                                let p_hi = _mm256_loadu_si256(
                                    sp.lo.as_ptr().add((k0 + 8) & sp.mask) as *const __m256i,
                                );
                                lo_v = mont_mul(lo_v, mont_mul(p_lo, hi));
                                hi_v = mont_mul(hi_v, mont_mul(p_hi, hi));
                            }
                            tiles[b / 8][0][b % 8] = lo_v;
                            tiles[b / 8][1][b % 8] = hi_v;
                        }
                        for rh in 0..2 {
                            transpose_8x8(&mut tiles[rh][0]);
                            transpose_8x8(&mut tiles[rh][1]);
                        }
                        for l in 0..16 {
                            let base = dst.add(i0 + REV4[l] * stride);
                            _mm256_storeu_si256(base as *mut __m256i, tiles[0][l / 8][l % 8]);
                            _mm256_storeu_si256(
                                base.add(8) as *mut __m256i,
                                tiles[1][l / 8][l % 8],
                            );
                        }
                    }
                });
            }
        });
    }

    /// Block size (log2, elements) of the block-local phase of the blocked
    /// parallel NTT: 2^16 x 4 B = 256 KB per block (L2-resident). The 16
    /// levels with `ppg < 2^16` only touch elements inside one block, so they
    /// cost ONE pass over DRAM regardless of how many sweeps run in-cache.
    pub const BLOCK_LOG2: u32 = 16;

    /// Sub-block size (log2) inside a phase-A block: the first 14 levels run
    /// on 2^14-element (64 KB) quarter-blocks so the hot footprint (data +
    /// the twiddle slice of the `ppg = 1` pass) stays far inside one core's
    /// L2 even when every core of the socket is busy — a 256 KB hot block
    /// measured 4x slower per block at 96 threads than at 64 (every in-block
    /// access went to DRAM), while the same block split in quarters does not.
    pub const SUB_BLOCK_LOG2: u32 = 14;

    /// The block-local levels (`ppg = 1 .. 2^15`) of the DIT NTT on the `b`-th
    /// 2^16-element block of a larger transform, hierarchically: for each of
    /// the four 2^14-element quarter-blocks (index `sb = 4b + q`) the shuffle
    /// passes `ppg = 1, 2, 4`, a radix-4 pass (8, 16), two radix-16 passes
    /// (32..256), (512..4096) and the single level 8192; then one radix-4
    /// pass (16384, 32768) over the whole block. Every twiddle group index is
    /// offset by the (sub-)block's position.
    #[inline(always)]
    pub unsafe fn ntt_block_local(
        a: *mut u32,
        b: usize,
        tw: *const u32,
        tw_ao: *const u32,
        tw_bo: *const u32,
    ) {
        let blk = 1usize << BLOCK_LOG2;
        let sub = 1usize << SUB_BLOCK_LOG2;
        debug_assert_eq!(blk, 4 * sub);
        for q in 0..4 {
            let sb = 4 * b + q;
            let p = a.add(q * sub);
            pass_ppg1(p, sub, tw.add(sb * sub / 2));
            pass_ppg2(p, sub, tw.add(sb * sub / 4));
            pass_ppg4(p, sub, tw.add(sb * sub / 8));
            // levels (8, 16)
            radix4_items(p, 8, tw, tw_ao, tw_bo, sb * (sub / 32), 0..sub / 32);
            // radix-16 passes (32..256), (512..4096)
            let mut ppg = 32usize;
            while ppg <= sub / 32 {
                let groups16 = sub / (16 * ppg);
                radix16_items(
                    p,
                    ppg,
                    tw,
                    tw_ao,
                    tw_bo,
                    sb * groups16,
                    0..groups16 * (ppg / 16),
                );
                ppg *= 16;
            }
            debug_assert_eq!(ppg, sub / 2);
            // the last quarter-block-local level (8192) alone
            radix2_items(p, ppg, tw, sb, 0..ppg / 8);
        }
        // levels (16384, 32768) over the block: one radix-4 pass, 4 streams
        let ppg = sub;
        radix4_items(a, ppg, tw, tw_ao, tw_bo, b, 0..ppg / 8);
    }

    /// Blocked WORKER-PARALLEL DIT NTT (`n >= 2^16`): phase A runs the 16
    /// block-local levels of every 256 KB block as independent tasks (ONE
    /// DRAM pass over the array, no barriers); phase B runs the remaining
    /// levels as radix-16 passes (four levels per DRAM sweep — a 2^24 column
    /// takes exactly two) chunked over the worker, plus at most one short
    /// leftover. Identical values to [`ntt_bitrev_to_natural`].
    pub unsafe fn ntt_bitrev_to_natural_blocked_parallel(
        a: &mut [u32],
        log_n: u32,
        tw: &[u32],
        tw_ao: &[u32],
        tw_bo: &[u32],
        worker: &Worker,
    ) {
        ntt_phase_a_blocks(a, tw, tw_ao, tw_bo, worker);
        ntt_phase_b_global(a, log_n, tw, tw_ao, tw_bo, worker);
    }

    /// Phase A of the blocked parallel NTT: the 16 block-local levels of
    /// every 2^16-element block, one block per task (no barriers inside).
    pub unsafe fn ntt_phase_a_blocks(
        a: &mut [u32],
        tw: &[u32],
        tw_ao: &[u32],
        tw_bo: &[u32],
        worker: &Worker,
    ) {
        let n = a.len();
        let blk = 1usize << BLOCK_LOG2;
        debug_assert!(n >= blk);
        let base_addr = a.as_mut_ptr() as usize;
        let t_addr = tw.as_ptr() as usize;
        let ao_addr = tw_ao.as_ptr() as usize;
        let bo_addr = tw_bo.as_ptr() as usize;
        let num_blocks = n / blk;
        worker.scope(num_blocks, |scope, geometry| {
            let (work, chunks) = (num_blocks, geometry.len());
            for thread_idx in 0..chunks {
                let (start, size) = balanced_chunk(work, chunks, thread_idx);
                spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| {
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
    }

    /// Phase B of the blocked parallel NTT: the levels above the block —
    /// radix-16 passes (four levels per DRAM sweep) chunked over the worker,
    /// then at most one short leftover (radix-4 pass and/or the twiddle-free
    /// tails).
    pub unsafe fn ntt_phase_b_global(
        a: &mut [u32],
        log_n: u32,
        tw: &[u32],
        tw_ao: &[u32],
        tw_bo: &[u32],
        worker: &Worker,
    ) {
        let n = a.len();
        let blk = 1usize << BLOCK_LOG2;
        debug_assert_eq!(n, 1usize << log_n);
        let base_addr = a.as_mut_ptr() as usize;
        let t_addr = tw.as_ptr() as usize;
        let ao_addr = tw_ao.as_ptr() as usize;
        let bo_addr = tw_bo.as_ptr() as usize;
        // phase B: global levels — radix-16 passes (four levels per DRAM
        // sweep) chunked over vector items, then the short leftover
        let mut ppg = blk;
        let mut levels_left = log_n - BLOCK_LOG2;
        while levels_left >= 4 {
            let items = n / 256; // (n / 16ppg groups) * (ppg / 16 lines)
            let cur_ppg = ppg;
            worker.scope(items, |scope, geometry| {
                let (work, chunks) = (items, geometry.len());
                for thread_idx in 0..chunks {
                    let (start, size) = balanced_chunk(work, chunks, thread_idx);
                    spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| {
                        radix16_items(
                            base_addr as *mut u32,
                            cur_ppg,
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
            // one radix-4 pass, then the twiddle-free final level below
            let items = n / 32;
            let cur_ppg = ppg;
            worker.scope(items, |scope, geometry| {
                let (work, chunks) = (items, geometry.len());
                for thread_idx in 0..chunks {
                    let (start, size) = balanced_chunk(work, chunks, thread_idx);
                    spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| {
                        radix4_items(
                            base_addr as *mut u32,
                            cur_ppg,
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
        let num_groups = match levels_left {
            0 => return,
            1 => 1,
            2 => 2,
            _ => unreachable!(),
        };
        match num_groups {
            2 => worker.scope(n / 32, |scope, geometry| {
                let (work, chunks) = (n / 32, geometry.len());
                for thread_idx in 0..chunks {
                    let (start, size) = balanced_chunk(work, chunks, thread_idx);
                    spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| {
                        tail_two_groups_items(
                            base_addr as *mut u32,
                            n,
                            t_addr as *const u32,
                            start..start + size,
                        );
                    });
                }
            }),
            1 => worker.scope(n / 16, |scope, geometry| {
                let (work, chunks) = (n / 16, geometry.len());
                for thread_idx in 0..chunks {
                    let (start, size) = balanced_chunk(work, chunks, thread_idx);
                    spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| {
                        tail_final_items(base_addr as *mut u32, n, start..start + size);
                    });
                }
            }),
            _ => unreachable!(),
        }
    }

    /// Fully-AVX2 GS DIT NTT on raw canonical values, `n >= 32`, with
    /// u64-accumulation radix-4 passes (needs the combined-twiddle tables).
    /// Identical values to `serial_ct_ntt_bitreversed_to_natural`.
    pub unsafe fn ntt_bitrev_to_natural(
        a: &mut [u32],
        log_n: u32,
        tw: &[u32],
        tw_ao: &[u32],
        tw_bo: &[u32],
    ) {
        let n = a.len();
        debug_assert_eq!(n, 1usize << log_n);
        debug_assert!(n >= 32);
        debug_assert!(n < 64 || (tw_ao.len() >= n / 32 && tw_bo.len() >= n / 32));
        let p = a.as_mut_ptr();
        let t = tw.as_ptr();
        pass_ppg1(p, n, t);
        pass_ppg2(p, n, t);
        pass_ppg4(p, n, t);
        let mut ppg = 8usize;
        let mut num_groups = n / 16;
        while num_groups >= 4 {
            radix4_pass_acc(p, ppg, num_groups, t, tw_ao.as_ptr(), tw_bo.as_ptr());
            ppg *= 4;
            num_groups /= 4;
        }
        match num_groups {
            2 => tail_two_groups(p, n, t),
            1 => tail_final(p, n),
            _ => unreachable!(),
        }
    }
}

/// Precomputed combined-twiddle tables for the u64-accumulation radix-4
/// passes: `ao[k] = mont(tw[2k], tw[k])`, `bo[k] = mont(tw[2k+1], tw[k])` for
/// `k < n/4` (the Ext4 kernels fuse from `ppg == 1`; the base-field kernel
/// reads a prefix). Depends only on the twiddle table — build once per
/// proving run and share across every batched call.
pub struct Avx2TwiddleExt {
    pub ao: Vec<u32>,
    pub bo: Vec<u32>,
}

impl Avx2TwiddleExt {
    pub fn build(twiddles: &[BabyBearField], n: usize) -> Self {
        let len = if n >= 8 { n / 4 } else { 0 };
        let mut ao = Vec::with_capacity(len);
        let mut bo = Vec::with_capacity(len);
        for k in 0..len {
            ao.push(mont_mul_scalar(
                twiddles[2 * k].raw_u32_value(),
                twiddles[k].raw_u32_value(),
            ));
            bo.push(mont_mul_scalar(
                twiddles[2 * k + 1].raw_u32_value(),
                twiddles[k].raw_u32_value(),
            ));
        }
        Self { ao, bo }
    }

    /// [`Self::build`] with the fill chunked over the worker (entries are
    /// independent functions of `k`); small tables run inline.
    pub fn build_parallel(twiddles: &[BabyBearField], n: usize, worker: &worker::Worker) -> Self {
        const PAR_THRESHOLD: usize = 1 << 10;
        let len = if n >= 8 { n / 4 } else { 0 };
        let mut ao: Vec<u32> = Vec::with_capacity(len);
        let mut bo: Vec<u32> = Vec::with_capacity(len);
        worker.scope_with_threshold(len, PAR_THRESHOLD, |scope, geometry| {
            let mut ao_rest = &mut ao.spare_capacity_mut()[..len];
            let mut bo_rest = &mut bo.spare_capacity_mut()[..len];
            for thread_idx in 0..geometry.num_chunks {
                let k0 = geometry.get_chunk_start_pos(thread_idx);
                let chunk = geometry.get_chunk_size(thread_idx);
                let (a, a_tail) = core::mem::take(&mut ao_rest).split_at_mut(chunk);
                let (b, b_tail) = core::mem::take(&mut bo_rest).split_at_mut(chunk);
                ao_rest = a_tail;
                bo_rest = b_tail;
                spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| {
                    for (i, (a, b)) in a.iter_mut().zip(b.iter_mut()).enumerate() {
                        let k = k0 + i;
                        a.write(mont_mul_scalar(
                            twiddles[2 * k].raw_u32_value(),
                            twiddles[k].raw_u32_value(),
                        ));
                        b.write(mont_mul_scalar(
                            twiddles[2 * k + 1].raw_u32_value(),
                            twiddles[k].raw_u32_value(),
                        ));
                    }
                });
            }
        });
        // SAFETY: the chunked fill initialized exactly the first `len`
        // entries of both vectors.
        unsafe {
            ao.set_len(len);
            bo.set_len(len);
        }
        Self { ao, bo }
    }
}

/// Serial LDE coset, fully AVX2: scaled copy (vector muls, split-power
/// factors), scalar bit-reversal, AVX2 u64-accumulation radix-4 NTT.
/// Byte-identical drop-in for `lde_coset_natural_seq_fused` on BabyBear;
/// degrades to the scalar reference below 32 elements (so EVERY poly size is
/// supported). `ext` must be built for a transform size >= `input.len()`.
pub fn lde_coset_avx2(
    input: &[BabyBearField],
    offset: BabyBearField,
    twiddles: &[BabyBearField],
    ext: &Avx2TwiddleExt,
) -> Vec<BabyBearField> {
    let n = input.len();
    if n < 32 {
        return crate::lde_coset_natural_seq_fused(input, offset, twiddles);
    }
    let log_n = n.trailing_zeros();

    let input_raw: &[u32] = unsafe { core::slice::from_raw_parts(input.as_ptr() as *const u32, n) };
    let tw_raw: &[u32] =
        unsafe { core::slice::from_raw_parts(twiddles.as_ptr() as *const u32, twiddles.len()) };

    let mut v: Vec<u32> = Vec::with_capacity(n);
    #[allow(clippy::uninit_vec)]
    unsafe {
        v.set_len(n)
    };

    if offset != BabyBearField::ONE {
        let sp = SplitPowersRaw::new(offset, log_n);
        unsafe {
            use core::arch::x86_64::*;
            let lo_len = sp.mask + 1; // >= 8 for n >= 32
            let src = input_raw.as_ptr();
            let dst = v.as_mut_ptr();
            let mut i = 0usize;
            while i < n {
                let hi = _mm256_set1_epi32(sp.hi[i >> sp.h] as i32);
                let block_end = i + lo_len;
                let mut j = i;
                while j < block_end {
                    let lo = _mm256_loadu_si256(sp.lo.as_ptr().add(j - i) as *const __m256i);
                    let f = avx2::mont_mul(lo, hi);
                    let x = _mm256_loadu_si256(src.add(j) as *const __m256i);
                    _mm256_storeu_si256(dst.add(j) as *mut __m256i, avx2::mont_mul(x, f));
                    j += 8;
                }
                i = block_end;
            }
        }
    } else {
        v.copy_from_slice(input_raw);
    }

    crate::utils::bitreverse_enumeration_inplace(&mut v);

    unsafe {
        avx2::ntt_bitrev_to_natural(&mut v, log_n, &tw_raw[..n / 2], &ext.ao, &ext.bo);
    }

    // SAFETY: repr(transparent), all values canonical.
    unsafe { core::mem::transmute::<Vec<u32>, Vec<BabyBearField>>(v) }
}

/// The "prepare" sweep of the parallel LDE: `dst[rev(k)] = src[k] * offset^k`
/// in ONE fused pass (scale + bit-reverse + copy).
pub fn lde_prepare_bitrev_scaled_into(
    src: &[u32],
    dst: &mut [u32],
    offset: BabyBearField,
    worker: &worker::Worker,
) {
    let log_n = src.len().trailing_zeros();
    let sp = (offset != BabyBearField::ONE).then(|| SplitPowersRaw::new(offset, log_n));
    unsafe { avx2::scaled_bitrev_copy_parallel(src, dst, sp.as_ref(), worker) };
}

/// Reference TWO-sweep variant of [`lde_prepare_bitrev_scaled_into`]: a
/// vectorized scaled copy, then the in-place parallel bit-reversal. Kept for
/// parity checks and kernel benchmarks.
pub fn lde_prepare_bitrev_scaled_two_sweeps_into(
    src: &[u32],
    dst: &mut [u32],
    offset: BabyBearField,
    worker: &worker::Worker,
) {
    let n = src.len();
    let log_n = n.trailing_zeros();
    let src_addr = src.as_ptr() as usize;
    let dst_addr = dst.as_mut_ptr() as usize;
    if offset != BabyBearField::ONE {
        let sp = SplitPowersRaw::new(offset, log_n);
        let sp_ref = &sp;
        worker.scope(n / 8, |scope, geometry| {
            let (work, chunks) = (n / 8, geometry.len());
            for thread_idx in 0..chunks {
                let (start, size) = balanced_chunk(work, chunks, thread_idx);
                spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                    use core::arch::x86_64::*;
                    let src = src_addr as *const u32;
                    let dst = dst_addr as *mut u32;
                    for v8 in start..start + size {
                        let i = v8 * 8;
                        let hi = _mm256_set1_epi32(sp_ref.hi[i >> sp_ref.h] as i32);
                        let lo = _mm256_loadu_si256(
                            sp_ref.lo.as_ptr().add(i & sp_ref.mask) as *const __m256i
                        );
                        let f = avx2::mont_mul(lo, hi);
                        let x = _mm256_loadu_si256(src.add(i) as *const __m256i);
                        _mm256_storeu_si256(dst.add(i) as *mut __m256i, avx2::mont_mul(x, f));
                    }
                });
            }
        });
    } else {
        worker.scope(n, |scope, geometry| {
            let (work, chunks) = (n, geometry.len());
            for thread_idx in 0..chunks {
                let (start, size) = balanced_chunk(work, chunks, thread_idx);
                spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                    core::ptr::copy_nonoverlapping(
                        (src_addr as *const u32).add(start),
                        (dst_addr as *mut u32).add(start),
                        size,
                    );
                });
            }
        });
    }
    crate::utils::parallel_bitreverse_enumeration_inplace(dst, worker);
}

/// Worker-PARALLEL base-field LDE coset (all threads on one coset): parallel
/// scaled copy, parallel bit-reversal, blocked parallel NTT. Byte-identical
/// to [`lde_coset_avx2`]; sizes below 2^16 run the serial kernel.
pub fn lde_coset_avx2_parallel(
    input: &[BabyBearField],
    offset: BabyBearField,
    twiddles: &[BabyBearField],
    ext: &Avx2TwiddleExt,
    worker: &worker::Worker,
) -> Vec<BabyBearField> {
    let n = input.len();
    if n < (1usize << avx2::BLOCK_LOG2) {
        return lde_coset_avx2(input, offset, twiddles, ext);
    }
    let log_n = n.trailing_zeros();
    let input_raw: &[u32] = unsafe { core::slice::from_raw_parts(input.as_ptr() as *const u32, n) };
    let tw_raw: &[u32] =
        unsafe { core::slice::from_raw_parts(twiddles.as_ptr() as *const u32, twiddles.len()) };

    let mut v: Vec<u32> = Vec::with_capacity(n);
    #[allow(clippy::uninit_vec)]
    unsafe {
        v.set_len(n)
    };
    // one sweep: scale + bit-reverse + copy (see `scaled_bitrev_copy_parallel`)
    lde_prepare_bitrev_scaled_into(input_raw, &mut v, offset, worker);

    unsafe {
        avx2::ntt_bitrev_to_natural_blocked_parallel(
            &mut v,
            log_n,
            &tw_raw[..n / 2],
            &ext.ao,
            &ext.bo,
            worker,
        );
    }

    // SAFETY: repr(transparent), all values canonical.
    unsafe { core::mem::transmute::<Vec<u32>, Vec<BabyBearField>>(v) }
}

/// AVX2 kernels for `BabyBearExt4` polynomials with BASE-field twiddles: one
/// extension element is one 128-bit half, a vector holds two consecutive
/// elements, and every butterfly is component-wise. See the module docs for
/// the pairing scheme. All kernels are byte-identical to their scalar
/// references and degrade to them below 16 elements.
pub mod ext4 {
    use super::avx2::{add, bias_all, fwd_core, inv_core, mont_mul, radix16_core, sub};
    use super::{balanced_chunk, spawn_chunk, Avx2TwiddleExt, SplitPowersRaw, P};
    use core::arch::x86_64::*;
    use field::baby_bear::base::BabyBearField;
    use field::baby_bear::ext4::BabyBearExt4;
    use field::{Field, FieldExtension, PrimeField};
    use worker::Worker;

    /// Two consecutive elements.
    #[inline(always)]
    unsafe fn ld2(p: *const BabyBearExt4) -> __m256i {
        _mm256_loadu_si256(p as *const __m256i)
    }
    #[inline(always)]
    unsafe fn st2(p: *mut BabyBearExt4, v: __m256i) {
        _mm256_storeu_si256(p as *mut __m256i, v)
    }
    /// One element in the low half (upper half zero).
    #[inline(always)]
    unsafe fn ld1(p: *const BabyBearExt4) -> __m256i {
        _mm256_zextsi128_si256(_mm_loadu_si128(p as *const __m128i))
    }
    #[inline(always)]
    unsafe fn st1(p: *mut BabyBearExt4, v: __m256i) {
        _mm_storeu_si128(p as *mut __m128i, _mm256_castsi256_si128(v))
    }
    /// One scalar broadcast to all 8 lanes.
    #[inline(always)]
    unsafe fn bc(x: u32) -> __m256i {
        _mm256_set1_epi32(x as i32)
    }
    /// Different scalars for the low (element A) and high (element B) halves.
    #[inline(always)]
    unsafe fn bc2(lo: u32, hi: u32) -> __m256i {
        _mm256_set_m128i(_mm_set1_epi32(hi as i32), _mm_set1_epi32(lo as i32))
    }
    /// `p * bo` per half, as u64 lanes.
    #[inline(always)]
    unsafe fn bias2(lo: u32, hi: u32) -> __m256i {
        let l = ((P as u64) * (lo as u64)) as i64;
        let h = ((P as u64) * (hi as u64)) as i64;
        _mm256_set_epi64x(h, h, l, l)
    }
    /// `[a.lo, b.lo]` and `[a.hi, b.hi]` (128-bit halves).
    #[inline(always)]
    unsafe fn lows(a: __m256i, b: __m256i) -> __m256i {
        _mm256_permute2x128_si256::<0x20>(a, b)
    }
    #[inline(always)]
    unsafe fn highs(a: __m256i, b: __m256i) -> __m256i {
        _mm256_permute2x128_si256::<0x31>(a, b)
    }

    /// Per-item twiddle set of the forward fused pass.
    #[inline(always)]
    unsafe fn fwd_tw_single(
        k2: usize,
        tw: *const u32,
        tw_ao: *const u32,
        tw_bo: *const u32,
    ) -> [__m256i; 6] {
        [
            bc(*tw.add(2 * k2)),
            bc(*tw.add(2 * k2 + 1)),
            bc(*tw.add(k2)),
            bc(*tw_ao.add(k2)),
            bc(*tw_bo.add(k2)),
            bias_all(*tw_bo.add(k2)),
        ]
    }
    #[inline(always)]
    unsafe fn fwd_tw_pair(
        k2: usize,
        tw: *const u32,
        tw_ao: *const u32,
        tw_bo: *const u32,
    ) -> [__m256i; 6] {
        [
            bc2(*tw.add(2 * k2), *tw.add(2 * k2 + 2)),
            bc2(*tw.add(2 * k2 + 1), *tw.add(2 * k2 + 3)),
            bc2(*tw.add(k2), *tw.add(k2 + 1)),
            bc2(*tw_ao.add(k2), *tw_ao.add(k2 + 1)),
            bc2(*tw_bo.add(k2), *tw_bo.add(k2 + 1)),
            bias2(*tw_bo.add(k2), *tw_bo.add(k2 + 1)),
        ]
    }

    /// FORWARD (GS, bit-reversed -> natural) radix-4 fused pass over element
    /// items; works for ANY `ppg >= 1`.
    #[inline(always)]
    unsafe fn fwd_radix4_items(
        a: *mut BabyBearExt4,
        ppg: usize,
        tw: *const u32,
        tw_ao: *const u32,
        tw_bo: *const u32,
        k2_offset: usize,
        item_range: core::ops::Range<usize>,
    ) {
        let (start, end) = (item_range.start, item_range.end);
        if ppg == 1 {
            // items are groups of 4 consecutive elements: pair two groups
            let mut t = start;
            while t + 1 < end {
                let j = 4 * t;
                let a01 = ld2(a.add(j));
                let a23 = ld2(a.add(j + 2));
                let b01 = ld2(a.add(j + 4));
                let b23 = ld2(a.add(j + 6));
                let [s_a, s_b, s_o, s_ao, s_bo, bias] =
                    fwd_tw_pair(t + k2_offset, tw, tw_ao, tw_bo);
                let (z0, z1, z2, z3) = fwd_core(
                    lows(a01, b01),
                    highs(a01, b01),
                    lows(a23, b23),
                    highs(a23, b23),
                    s_a,
                    s_b,
                    s_o,
                    s_ao,
                    s_bo,
                    bias,
                );
                st2(a.add(j), lows(z0, z1));
                st2(a.add(j + 2), lows(z2, z3));
                st2(a.add(j + 4), highs(z0, z1));
                st2(a.add(j + 6), highs(z2, z3));
                t += 2;
            }
            if t < end {
                let j = 4 * t;
                let [s_a, s_b, s_o, s_ao, s_bo, bias] =
                    fwd_tw_single(t + k2_offset, tw, tw_ao, tw_bo);
                let (z0, z1, z2, z3) = fwd_core(
                    ld1(a.add(j)),
                    ld1(a.add(j + 1)),
                    ld1(a.add(j + 2)),
                    ld1(a.add(j + 3)),
                    s_a,
                    s_b,
                    s_o,
                    s_ao,
                    s_bo,
                    bias,
                );
                st1(a.add(j), z0);
                st1(a.add(j + 1), z1);
                st1(a.add(j + 2), z2);
                st1(a.add(j + 3), z3);
            }
            return;
        }
        // ppg >= 2: items (t, t+1) with t even share a group and are contiguous
        let mut t = start;
        let single = |t: usize| {
            let k2 = t / ppg;
            let j = k2 * (ppg * 4) + (t % ppg);
            let [s_a, s_b, s_o, s_ao, s_bo, bias] = fwd_tw_single(k2 + k2_offset, tw, tw_ao, tw_bo);
            let (z0, z1, z2, z3) = fwd_core(
                ld1(a.add(j)),
                ld1(a.add(j + ppg)),
                ld1(a.add(j + 2 * ppg)),
                ld1(a.add(j + 3 * ppg)),
                s_a,
                s_b,
                s_o,
                s_ao,
                s_bo,
                bias,
            );
            st1(a.add(j), z0);
            st1(a.add(j + ppg), z1);
            st1(a.add(j + 2 * ppg), z2);
            st1(a.add(j + 3 * ppg), z3);
        };
        if t < end && t % 2 == 1 {
            single(t);
            t += 1;
        }
        while t + 1 < end {
            let k2 = t / ppg;
            let j = k2 * (ppg * 4) + (t % ppg);
            let [s_a, s_b, s_o, s_ao, s_bo, bias] = fwd_tw_single(k2 + k2_offset, tw, tw_ao, tw_bo);
            let (z0, z1, z2, z3) = fwd_core(
                ld2(a.add(j)),
                ld2(a.add(j + ppg)),
                ld2(a.add(j + 2 * ppg)),
                ld2(a.add(j + 3 * ppg)),
                s_a,
                s_b,
                s_o,
                s_ao,
                s_bo,
                bias,
            );
            st2(a.add(j), z0);
            st2(a.add(j + ppg), z1);
            st2(a.add(j + 2 * ppg), z2);
            st2(a.add(j + 3 * ppg), z3);
            t += 2;
        }
        if t < end {
            single(t);
        }
    }

    /// FORWARD radix-16 fused pass (levels `ppg .. 8ppg`) over LINE items:
    /// item `t` is the 16ppg-group `k4 = t / (ppg/4)` (twiddle index
    /// `k4 + k4_offset`) and the 64-byte line `jl` (four elements, two
    /// vectors per stream) within it; `ppg >= 4`. Two in-register radix-4
    /// stages through [`radix16_core`] with the same twiddle sets as
    /// [`fwd_radix4_items`]; line-complete because the 16 streams alias in
    /// the same cache sets.
    #[inline(always)]
    unsafe fn fwd_radix16_items(
        a: *mut BabyBearExt4,
        ppg: usize,
        tw: *const u32,
        tw_ao: *const u32,
        tw_bo: *const u32,
        k4_offset: usize,
        item_range: core::ops::Range<usize>,
    ) {
        debug_assert!(ppg >= 4);
        let lines_per_group = ppg / 4;
        let mut t = item_range.start;
        while t < item_range.end {
            let k4 = t / lines_per_group;
            let jl = t % lines_per_group;
            let kg = k4 + k4_offset;
            let twa: [[__m256i; 6]; 4] =
                core::array::from_fn(|q| fwd_tw_single(4 * kg + q, tw, tw_ao, tw_bo));
            let twb = fwd_tw_single(kg, tw, tw_ao, tw_bo);
            let run = (lines_per_group - jl).min(item_range.end - t);
            let mut j = k4 * ppg * 16 + jl * 4;
            for _ in 0..run {
                let mut x0: [__m256i; 16] = core::array::from_fn(|i| ld2(a.add(j + i * ppg)));
                let mut x1: [__m256i; 16] = core::array::from_fn(|i| ld2(a.add(j + 2 + i * ppg)));
                radix16_core(&mut x0, &twa, &twb);
                radix16_core(&mut x1, &twa, &twb);
                for i in 0..16 {
                    st2(a.add(j + i * ppg), x0[i]);
                    st2(a.add(j + 2 + i * ppg), x1[i]);
                }
                j += 4;
            }
            t += run;
        }
    }

    /// Forward fused tail (`num_groups == 2`): groups 0/1 + final level.
    #[inline(always)]
    unsafe fn fwd_tail_two_groups(
        a: *mut BabyBearExt4,
        n: usize,
        tw: *const u32,
        jr: core::ops::Range<usize>,
    ) {
        let q = n / 4;
        let s_a = bc(*tw);
        let s_b = bc(*tw.add(1));
        let (start, end) = (jr.start, jr.end);
        let mut j = start;
        let body = |j: usize, two: bool| {
            let (x0, x1, x2, x3) = if two {
                (
                    ld2(a.add(j)),
                    ld2(a.add(j + q)),
                    ld2(a.add(j + 2 * q)),
                    ld2(a.add(j + 3 * q)),
                )
            } else {
                (
                    ld1(a.add(j)),
                    ld1(a.add(j + q)),
                    ld1(a.add(j + 2 * q)),
                    ld1(a.add(j + 3 * q)),
                )
            };
            let y0 = add(x0, x1);
            let y1 = mont_mul(sub(x0, x1), s_a);
            let y2 = add(x2, x3);
            let y3 = mont_mul(sub(x2, x3), s_b);
            let (o0, o2, o1, o3) = (add(y0, y2), sub(y0, y2), add(y1, y3), sub(y1, y3));
            if two {
                st2(a.add(j), o0);
                st2(a.add(j + 2 * q), o2);
                st2(a.add(j + q), o1);
                st2(a.add(j + 3 * q), o3);
            } else {
                st1(a.add(j), o0);
                st1(a.add(j + 2 * q), o2);
                st1(a.add(j + q), o1);
                st1(a.add(j + 3 * q), o3);
            }
        };
        while j + 1 < end {
            body(j, true);
            j += 2;
        }
        if j < end {
            body(j, false);
        }
    }

    #[inline(always)]
    unsafe fn fwd_tail_final(a: *mut BabyBearExt4, n: usize, jr: core::ops::Range<usize>) {
        let half = n / 2;
        let (start, end) = (jr.start, jr.end);
        let mut j = start;
        while j + 1 < end {
            let u = ld2(a.add(j));
            let v = ld2(a.add(j + half));
            st2(a.add(j), add(u, v));
            st2(a.add(j + half), sub(u, v));
            j += 2;
        }
        if j < end {
            let u = ld1(a.add(j));
            let v = ld1(a.add(j + half));
            st1(a.add(j), add(u, v));
            st1(a.add(j + half), sub(u, v));
        }
    }

    /// Serial forward NTT (bit-reversed -> natural), byte-identical to
    /// `serial_ct_ntt_bitreversed_to_natural` over Ext4.
    pub unsafe fn ntt_fwd(a: &mut [BabyBearExt4], tw_raw: &[u32], ext: &Avx2TwiddleExt) {
        let n = a.len();
        let p = a.as_mut_ptr();
        let t = tw_raw.as_ptr();
        let mut ppg = 1usize;
        let mut num_groups = n / 2;
        while num_groups >= 4 {
            fwd_radix4_items(
                p,
                ppg,
                t,
                ext.ao.as_ptr(),
                ext.bo.as_ptr(),
                0,
                0..(num_groups / 2) * ppg,
            );
            ppg *= 4;
            num_groups /= 4;
        }
        match num_groups {
            2 => fwd_tail_two_groups(p, n, t, 0..n / 4),
            1 => fwd_tail_final(p, n, 0..n / 2),
            _ => unreachable!(),
        }
    }

    /// Block size (log2, elements) of the block-local phase of the blocked
    /// parallel Ext4 NTT: 2^13 x 16 B = 128 KB. The 12 levels with
    /// `ppg < 2^12` (six fused pairs from `ppg = 1`) are block-local.
    pub const BLOCK_LOG2_EXT: u32 = 13;

    /// Block-local fused pairs `(1,2) .. (1024,2048)` on the `b`-th 2^13-element
    /// block of a larger transform (twiddle group indices offset by the block).
    #[inline(always)]
    unsafe fn ntt_fwd_block_local(
        a: *mut BabyBearExt4,
        b: usize,
        tw: *const u32,
        tw_ao: *const u32,
        tw_bo: *const u32,
    ) {
        let blk = 1usize << BLOCK_LOG2_EXT;
        let mut ppg = 1usize;
        while ppg < blk / 2 {
            let outer_groups = blk / (4 * ppg);
            fwd_radix4_items(
                a,
                ppg,
                tw,
                tw_ao,
                tw_bo,
                b * outer_groups,
                0..outer_groups * ppg,
            );
            ppg *= 4;
        }
        debug_assert_eq!(ppg, blk / 2);
    }

    /// Blocked WORKER-PARALLEL forward NTT (`n >= 2^14`): the 12 block-local
    /// levels of every 128 KB block as independent tasks (one DRAM pass, no
    /// barriers), then the remaining levels as radix-16 line passes (four
    /// levels per DRAM sweep) chunked over the worker, plus at most one short
    /// leftover. Identical values to [`ntt_fwd`].
    pub unsafe fn ntt_fwd_blocked_parallel(
        a: &mut [BabyBearExt4],
        tw_raw: &[u32],
        ext: &Avx2TwiddleExt,
        worker: &Worker,
    ) {
        let n = a.len();
        let blk = 1usize << BLOCK_LOG2_EXT;
        debug_assert!(n >= 2 * blk);
        let log_n = n.trailing_zeros();
        let base_addr = a.as_mut_ptr() as usize;
        let (t_addr, ao_addr, bo_addr) = (
            tw_raw.as_ptr() as usize,
            ext.ao.as_ptr() as usize,
            ext.bo.as_ptr() as usize,
        );

        let num_blocks = n / blk;
        worker.scope(num_blocks, |scope, geometry| {
            let (work, chunks) = (num_blocks, geometry.len());
            for thread_idx in 0..chunks {
                let (start, size) = balanced_chunk(work, chunks, thread_idx);
                spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                    for b in start..start + size {
                        ntt_fwd_block_local(
                            (base_addr as *mut BabyBearExt4).add(b * blk),
                            b,
                            t_addr as *const u32,
                            ao_addr as *const u32,
                            bo_addr as *const u32,
                        );
                    }
                });
            }
        });

        // global levels: radix-16 line passes (four levels per DRAM sweep),
        // then at most one short leftover
        let mut ppg = blk / 2;
        let mut levels_left = log_n - (BLOCK_LOG2_EXT - 1);
        while levels_left >= 4 {
            let items = n / 64; // (n / 16ppg groups) * (ppg / 4 lines)
            let cur_ppg = ppg;
            worker.scope(items, |scope, geometry| {
                let (work, chunks) = (items, geometry.len());
                for thread_idx in 0..chunks {
                    let (start, size) = balanced_chunk(work, chunks, thread_idx);
                    spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                        fwd_radix16_items(
                            base_addr as *mut BabyBearExt4,
                            cur_ppg,
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
            let items = n / 4;
            let cur_ppg = ppg;
            worker.scope(items, |scope, geometry| {
                let (work, chunks) = (items, geometry.len());
                for thread_idx in 0..chunks {
                    let (start, size) = balanced_chunk(work, chunks, thread_idx);
                    spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                        fwd_radix4_items(
                            base_addr as *mut BabyBearExt4,
                            cur_ppg,
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
            2 => worker.scope(n / 4, |scope, geometry| {
                let (work, chunks) = (n / 4, geometry.len());
                for thread_idx in 0..chunks {
                    let (start, size) = balanced_chunk(work, chunks, thread_idx);
                    spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                        fwd_tail_two_groups(
                            base_addr as *mut BabyBearExt4,
                            n,
                            t_addr as *const u32,
                            start..start + size,
                        );
                    });
                }
            }),
            1 => worker.scope(n / 2, |scope, geometry| {
                let (work, chunks) = (n / 2, geometry.len());
                for thread_idx in 0..chunks {
                    let (start, size) = balanced_chunk(work, chunks, thread_idx);
                    spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                        fwd_tail_final(base_addr as *mut BabyBearExt4, n, start..start + size);
                    });
                }
            }),
            _ => unreachable!(),
        }
    }

    /// Serial LDE coset over Ext4 — drop-in for `lde_coset_natural_seq_fused`
    /// (byte-identical); sizes below 16 degrade to it.
    pub fn lde_coset(
        input: &[BabyBearExt4],
        offset: BabyBearField,
        twiddles: &[BabyBearField],
        ext: &Avx2TwiddleExt,
    ) -> Vec<BabyBearExt4> {
        let n = input.len();
        let mut v: Vec<BabyBearExt4> = Vec::with_capacity(n);
        #[allow(clippy::uninit_vec)]
        unsafe {
            v.set_len(n)
        };
        lde_coset_into(input, offset, twiddles, ext, &mut v);
        v
    }

    /// Scaled copy `dst[i] = src[i] * f_i` over a range (two elements per
    /// vector; the range is even-length for every caller except the last
    /// worker chunk, handled by the single tail).
    #[inline(always)]
    unsafe fn scaled_copy_range(
        src: *const BabyBearExt4,
        dst: *mut BabyBearExt4,
        sp: &SplitPowersRaw,
        range: core::ops::Range<usize>,
    ) {
        let (start, end) = (range.start, range.end);
        let f_at = |i: usize| super::mont_mul_scalar(sp.lo[i & sp.mask], sp.hi[i >> sp.h]);
        let mut i = start;
        while i + 1 < end {
            let f = bc2(f_at(i), f_at(i + 1));
            st2(dst.add(i), mont_mul(ld2(src.add(i)), f));
            i += 2;
        }
        if i < end {
            st1(dst.add(i), mont_mul(ld1(src.add(i)), bc(f_at(i))));
        }
    }

    /// [`lde_coset`] writing into a caller-provided WRITE-FIRST buffer.
    pub fn lde_coset_into(
        input: &[BabyBearExt4],
        offset: BabyBearField,
        twiddles: &[BabyBearField],
        ext: &Avx2TwiddleExt,
        out: &mut [BabyBearExt4],
    ) {
        let n = input.len();
        assert_eq!(out.len(), n);
        if n < 16 {
            return crate::lde_coset_natural_seq_fused_into(input, offset, twiddles, out);
        }
        let log_n = n.trailing_zeros();
        let tw_raw: &[u32] =
            unsafe { core::slice::from_raw_parts(twiddles.as_ptr() as *const u32, twiddles.len()) };

        if offset != BabyBearField::ONE {
            let sp = SplitPowersRaw::new(offset, log_n);
            unsafe {
                scaled_copy_range(input.as_ptr(), out.as_mut_ptr(), &sp, 0..n);
            }
        } else {
            out.copy_from_slice(input);
        }
        crate::utils::bitreverse_enumeration_inplace(out);
        unsafe {
            ntt_fwd(out, &tw_raw[..n / 2], ext);
        }
    }

    /// Worker-PARALLEL LDE coset over Ext4: every pass worker-wide with a
    /// barrier between passes. Byte-identical to the serial pipeline; falls
    /// back to it below 2^12 elements.
    pub fn lde_coset_parallel(
        input: &[BabyBearExt4],
        offset: BabyBearField,
        twiddles: &[BabyBearField],
        ext: &Avx2TwiddleExt,
        worker: &Worker,
    ) -> Vec<BabyBearExt4> {
        let n = input.len();
        let mut v: Vec<BabyBearExt4> = Vec::with_capacity(n);
        #[allow(clippy::uninit_vec)]
        unsafe {
            v.set_len(n)
        };
        lde_coset_parallel_into(input, offset, twiddles, ext, worker, &mut v);
        v
    }

    /// [`lde_coset_parallel`] writing into a caller-provided WRITE-FIRST buffer.
    pub fn lde_coset_parallel_into(
        input: &[BabyBearExt4],
        offset: BabyBearField,
        twiddles: &[BabyBearField],
        ext: &Avx2TwiddleExt,
        worker: &Worker,
        out: &mut [BabyBearExt4],
    ) {
        let n = input.len();
        assert_eq!(out.len(), n);
        const PAR_THRESHOLD: usize = 1 << 12;
        if n < PAR_THRESHOLD {
            return lde_coset_into(input, offset, twiddles, ext, out);
        }
        let log_n = n.trailing_zeros();
        let tw_raw: &[u32] =
            unsafe { core::slice::from_raw_parts(twiddles.as_ptr() as *const u32, twiddles.len()) };

        let src_addr = input.as_ptr() as usize;
        let dst_addr = out.as_mut_ptr() as usize;

        if offset != BabyBearField::ONE {
            let sp = SplitPowersRaw::new(offset, log_n);
            let sp_ref = &sp;
            worker.scope(n, |scope, geometry| {
                let (work, chunks) = (n, geometry.len());
                for thread_idx in 0..chunks {
                    let (start, size) = balanced_chunk(work, chunks, thread_idx);
                    spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                        scaled_copy_range(
                            src_addr as *const BabyBearExt4,
                            dst_addr as *mut BabyBearExt4,
                            sp_ref,
                            start..start + size,
                        );
                    });
                }
            });
        } else {
            worker.scope(n, |scope, geometry| {
                let (work, chunks) = (n, geometry.len());
                for thread_idx in 0..chunks {
                    let (start, size) = balanced_chunk(work, chunks, thread_idx);
                    spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                        let src = src_addr as *const BabyBearExt4;
                        let dst = dst_addr as *mut BabyBearExt4;
                        core::ptr::copy_nonoverlapping(src.add(start), dst.add(start), size);
                    });
                }
            });
        }

        crate::utils::parallel_bitreverse_enumeration_inplace(out, worker);

        // blocked parallel NTT (cache-resident low levels, then global passes)
        if n >= (2usize << BLOCK_LOG2_EXT) {
            unsafe {
                ntt_fwd_blocked_parallel(out, &tw_raw[..n / 2], ext, worker);
            }
            return;
        }

        // small parallel sizes: one worker scope per fused pass
        let tw = &tw_raw[..n / 2];
        let (tw_addr, ao_addr, bo_addr) = (
            tw.as_ptr() as usize,
            ext.ao.as_ptr() as usize,
            ext.bo.as_ptr() as usize,
        );
        let base_addr = out.as_mut_ptr() as usize;
        let mut ppg = 1usize;
        let mut num_groups = n / 2;
        while num_groups >= 4 {
            let items = (num_groups / 2) * ppg;
            let cur_ppg = ppg;
            worker.scope(items, |scope, geometry| {
                let (work, chunks) = (items, geometry.len());
                for thread_idx in 0..chunks {
                    let (start, size) = balanced_chunk(work, chunks, thread_idx);
                    spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                        fwd_radix4_items(
                            base_addr as *mut BabyBearExt4,
                            cur_ppg,
                            tw_addr as *const u32,
                            ao_addr as *const u32,
                            bo_addr as *const u32,
                            0,
                            start..start + size,
                        );
                    });
                }
            });
            ppg *= 4;
            num_groups /= 4;
        }
        match num_groups {
            2 => {
                worker.scope(n / 4, |scope, geometry| {
                    let (work, chunks) = (n / 4, geometry.len());
                    for thread_idx in 0..chunks {
                        let (start, size) = balanced_chunk(work, chunks, thread_idx);
                        spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                            fwd_tail_two_groups(
                                base_addr as *mut BabyBearExt4,
                                n,
                                tw_addr as *const u32,
                                start..start + size,
                            );
                        });
                    }
                });
            }
            1 => {
                worker.scope(n / 2, |scope, geometry| {
                    let (work, chunks) = (n / 2, geometry.len());
                    for thread_idx in 0..chunks {
                        let (start, size) = balanced_chunk(work, chunks, thread_idx);
                        spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                            fwd_tail_final(base_addr as *mut BabyBearExt4, n, start..start + size);
                        });
                    }
                });
            }
            _ => unreachable!(),
        }
    }

    /// Per-item twiddle set of the inverse fused pass.
    #[inline(always)]
    unsafe fn inv_tw_single(
        k: usize,
        tw: *const u32,
        tw_ao: *const u32,
        tw_bo: *const u32,
    ) -> [__m256i; 6] {
        [
            bc(*tw.add(k)),
            bc(*tw.add(2 * k)),
            bc(*tw.add(2 * k + 1)),
            bc(*tw_ao.add(k)),
            bc(*tw_bo.add(k)),
            bias_all(*tw_bo.add(k)),
        ]
    }
    #[inline(always)]
    unsafe fn inv_tw_pair(
        k: usize,
        tw: *const u32,
        tw_ao: *const u32,
        tw_bo: *const u32,
    ) -> [__m256i; 6] {
        [
            bc2(*tw.add(k), *tw.add(k + 1)),
            bc2(*tw.add(2 * k), *tw.add(2 * k + 2)),
            bc2(*tw.add(2 * k + 1), *tw.add(2 * k + 3)),
            bc2(*tw_ao.add(k), *tw_ao.add(k + 1)),
            bc2(*tw_bo.add(k), *tw_bo.add(k + 1)),
            bias2(*tw_bo.add(k), *tw_bo.add(k + 1)),
        ]
    }

    /// INVERSE-direction (CT, natural -> bit-reversed) radix-4 fused pass with
    /// u64 accumulation; `half_d` = distance of the SECOND stage = d/2.
    #[inline(always)]
    unsafe fn inv_radix4_items(
        a: *mut BabyBearExt4,
        half_d: usize,
        tw: *const u32,
        tw_ao: *const u32,
        tw_bo: *const u32,
        item_range: core::ops::Range<usize>,
    ) {
        let (start, end) = (item_range.start, item_range.end);
        if half_d == 1 {
            let mut t = start;
            while t + 1 < end {
                let j = 4 * t;
                let a01 = ld2(a.add(j));
                let a23 = ld2(a.add(j + 2));
                let b01 = ld2(a.add(j + 4));
                let b23 = ld2(a.add(j + 6));
                let [s, s_a, s_b, s_ao, s_bo, bias] = inv_tw_pair(t, tw, tw_ao, tw_bo);
                let (z0, z1, z2, z3) = inv_core(
                    lows(a01, b01),
                    highs(a01, b01),
                    lows(a23, b23),
                    highs(a23, b23),
                    s,
                    s_a,
                    s_b,
                    s_ao,
                    s_bo,
                    bias,
                );
                st2(a.add(j), lows(z0, z1));
                st2(a.add(j + 2), lows(z2, z3));
                st2(a.add(j + 4), highs(z0, z1));
                st2(a.add(j + 6), highs(z2, z3));
                t += 2;
            }
            if t < end {
                let j = 4 * t;
                let [s, s_a, s_b, s_ao, s_bo, bias] = inv_tw_single(t, tw, tw_ao, tw_bo);
                let (z0, z1, z2, z3) = inv_core(
                    ld1(a.add(j)),
                    ld1(a.add(j + 1)),
                    ld1(a.add(j + 2)),
                    ld1(a.add(j + 3)),
                    s,
                    s_a,
                    s_b,
                    s_ao,
                    s_bo,
                    bias,
                );
                st1(a.add(j), z0);
                st1(a.add(j + 1), z1);
                st1(a.add(j + 2), z2);
                st1(a.add(j + 3), z3);
            }
            return;
        }
        let mut t = start;
        let single = |t: usize| {
            let k = t / half_d;
            let j = k * (half_d * 4) + (t % half_d);
            let [s, s_a, s_b, s_ao, s_bo, bias] = inv_tw_single(k, tw, tw_ao, tw_bo);
            let (z0, z1, z2, z3) = inv_core(
                ld1(a.add(j)),
                ld1(a.add(j + half_d)),
                ld1(a.add(j + 2 * half_d)),
                ld1(a.add(j + 3 * half_d)),
                s,
                s_a,
                s_b,
                s_ao,
                s_bo,
                bias,
            );
            st1(a.add(j), z0);
            st1(a.add(j + half_d), z1);
            st1(a.add(j + 2 * half_d), z2);
            st1(a.add(j + 3 * half_d), z3);
        };
        if t < end && t % 2 == 1 {
            single(t);
            t += 1;
        }
        while t + 1 < end {
            let k = t / half_d;
            let j = k * (half_d * 4) + (t % half_d);
            let [s, s_a, s_b, s_ao, s_bo, bias] = inv_tw_single(k, tw, tw_ao, tw_bo);
            let (z0, z1, z2, z3) = inv_core(
                ld2(a.add(j)),
                ld2(a.add(j + half_d)),
                ld2(a.add(j + 2 * half_d)),
                ld2(a.add(j + 3 * half_d)),
                s,
                s_a,
                s_b,
                s_ao,
                s_bo,
                bias,
            );
            st2(a.add(j), z0);
            st2(a.add(j + half_d), z1);
            st2(a.add(j + 2 * half_d), z2);
            st2(a.add(j + 3 * half_d), z3);
            t += 2;
        }
        if t < end {
            single(t);
        }
    }

    /// First inverse stage (omega = 1) fused with the second (distance n/4,
    /// twiddles tw[0], tw[1]).
    #[inline(always)]
    unsafe fn inv_head_two_stages(
        a: *mut BabyBearExt4,
        n: usize,
        tw: *const u32,
        jr: core::ops::Range<usize>,
    ) {
        let q = n / 4;
        let s_a = bc(*tw);
        let s_b = bc(*tw.add(1));
        let (start, end) = (jr.start, jr.end);
        let body = |j: usize, two: bool| {
            let (x0, x1, x2, x3) = if two {
                (
                    ld2(a.add(j)),
                    ld2(a.add(j + q)),
                    ld2(a.add(j + 2 * q)),
                    ld2(a.add(j + 3 * q)),
                )
            } else {
                (
                    ld1(a.add(j)),
                    ld1(a.add(j + q)),
                    ld1(a.add(j + 2 * q)),
                    ld1(a.add(j + 3 * q)),
                )
            };
            let y0 = add(x0, x2);
            let y2 = sub(x0, x2);
            let y1 = add(x1, x3);
            let y3 = sub(x1, x3);
            let t1 = mont_mul(y1, s_a);
            let t3 = mont_mul(y3, s_b);
            let (o0, o1, o2, o3) = (add(y0, t1), sub(y0, t1), add(y2, t3), sub(y2, t3));
            if two {
                st2(a.add(j), o0);
                st2(a.add(j + q), o1);
                st2(a.add(j + 2 * q), o2);
                st2(a.add(j + 3 * q), o3);
            } else {
                st1(a.add(j), o0);
                st1(a.add(j + q), o1);
                st1(a.add(j + 2 * q), o2);
                st1(a.add(j + 3 * q), o3);
            }
        };
        let mut j = start;
        while j + 1 < end {
            body(j, true);
            j += 2;
        }
        if j < end {
            body(j, false);
        }
    }

    /// First inverse stage alone (omega = 1, distance n/2).
    #[inline(always)]
    unsafe fn inv_head_single(a: *mut BabyBearExt4, n: usize, jr: core::ops::Range<usize>) {
        let half = n / 2;
        let (start, end) = (jr.start, jr.end);
        let mut j = start;
        while j + 1 < end {
            let u = ld2(a.add(j));
            let v = ld2(a.add(j + half));
            st2(a.add(j), add(u, v));
            st2(a.add(j + half), sub(u, v));
            j += 2;
        }
        if j < end {
            let u = ld1(a.add(j));
            let v = ld1(a.add(j + half));
            st1(a.add(j), add(u, v));
            st1(a.add(j + half), sub(u, v));
        }
    }

    /// Worker-parallel `main-domain evals -> monomial coefficients` for the
    /// O(1) batched Ext4 poly: parallel inverse NTT (natural -> bit-reversed,
    /// CT direction, radix-4 fused + u64-acc), parallel `1/N` scaling,
    /// parallel bit-reversal. `inv_ext` must be built from the INVERSE
    /// twiddle table. Byte-identical to `cache_friendly_ntt_natural_to_
    /// bitreversed` + scale + bitrev; sizes below 2^12 run the reference.
    pub fn monomial_form_from_main_domain(
        mut v: Vec<BabyBearExt4>,
        inverse_twiddles: &[BabyBearField],
        inv_ext: &Avx2TwiddleExt,
        worker: &Worker,
    ) -> Vec<BabyBearExt4> {
        let n = v.len();
        let log_n = n.trailing_zeros();
        let size_inv = BabyBearField::from_u32_unchecked(n as u32)
            .inverse()
            .unwrap();
        const PAR_THRESHOLD: usize = 1 << 12;
        if n < PAR_THRESHOLD {
            crate::naive::cache_friendly_ntt_natural_to_bitreversed(
                &mut v,
                log_n,
                &inverse_twiddles[..(n / 2).max(1)],
            );
            for el in v.iter_mut() {
                el.mul_assign_by_base(&size_inv);
            }
            crate::utils::bitreverse_enumeration_inplace(&mut v);
            return v;
        }

        let tw_raw: &[u32] =
            unsafe { core::slice::from_raw_parts(inverse_twiddles.as_ptr() as *const u32, n / 2) };
        let base_addr = v.as_mut_ptr() as usize;

        let mut dist = n / 2;
        let mut stages_left = log_n;
        if log_n % 2 == 0 {
            worker.scope(n / 4, |scope, geometry| {
                let (work, chunks) = (n / 4, geometry.len());
                for thread_idx in 0..chunks {
                    let (start, size) = balanced_chunk(work, chunks, thread_idx);
                    let tw_addr = tw_raw.as_ptr() as usize;
                    spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                        inv_head_two_stages(
                            base_addr as *mut BabyBearExt4,
                            n,
                            tw_addr as *const u32,
                            start..start + size,
                        );
                    });
                }
            });
            dist /= 4;
            stages_left -= 2;
        } else {
            worker.scope(n / 2, |scope, geometry| {
                let (work, chunks) = (n / 2, geometry.len());
                for thread_idx in 0..chunks {
                    let (start, size) = balanced_chunk(work, chunks, thread_idx);
                    spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                        inv_head_single(base_addr as *mut BabyBearExt4, n, start..start + size);
                    });
                }
            });
            dist /= 2;
            stages_left -= 1;
        }

        while stages_left >= 2 {
            debug_assert!(dist >= 2);
            let half_d = dist / 2;
            let items = (n / (2 * dist)) * half_d;
            assert_eq!(items, n / 4);
            worker.scope(items, |scope, geometry| {
                let (work, chunks) = (items, geometry.len());
                for thread_idx in 0..chunks {
                    let (start, size) = balanced_chunk(work, chunks, thread_idx);
                    let tw_addr = tw_raw.as_ptr() as usize;
                    let (ao, bo) = (inv_ext.ao.as_ptr() as usize, inv_ext.bo.as_ptr() as usize);
                    spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                        inv_radix4_items(
                            base_addr as *mut BabyBearExt4,
                            half_d,
                            tw_addr as *const u32,
                            ao as *const u32,
                            bo as *const u32,
                            start..start + size,
                        );
                    });
                }
            });
            dist /= 4;
            stages_left -= 2;
        }
        debug_assert_eq!(stages_left, 0, "stage pairing above must consume all");

        // parallel scale by 1/N + parallel bitrev
        let f_bits = size_inv.raw_u32_value();
        worker.scope(n, |scope, geometry| {
            let (work, chunks) = (n, geometry.len());
            for thread_idx in 0..chunks {
                let (start, size) = balanced_chunk(work, chunks, thread_idx);
                spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                    let f = bc(f_bits);
                    let base = base_addr as *mut BabyBearExt4;
                    let end = start + size;
                    let mut i = start;
                    while i + 1 < end {
                        st2(base.add(i), mont_mul(ld2(base.add(i)), f));
                        i += 2;
                    }
                    if i < end {
                        st1(base.add(i), mont_mul(ld1(base.add(i)), f));
                    }
                });
            }
        });
        crate::utils::parallel_bitreverse_enumeration_inplace(&mut v, worker);
        v
    }

    /// Leaf FOLDING (evaluation form -> multilinear-coefficient form) for one
    /// whole coset of Ext4 values: the per-leaf `evals_to_multilinear_coeffs`
    /// butterfly network, two LEAVES per vector (slot `k` of leaves `L` and
    /// `L+1` are adjacent in the column), the leaf held in registers/stack
    /// across all stages, with the per-pair `root * 2^-1` twiddles FUSED into
    /// one scalar Montgomery product per table entry (identical canonical
    /// values). `values_per_leaf` must be a power of two in `2..=32`.
    #[inline(always)]
    unsafe fn fold_leaf_range(
        column: *mut BabyBearExt4,
        offsets: &[usize],
        hp_raw: &[u32],
        two_inv_raw: u32,
        root_invs_raw: &[u32],
        leaf_range: core::ops::Range<usize>,
    ) {
        let n = offsets.len();
        let rounds = n.trailing_zeros() as usize;
        debug_assert!(n >= 2 && n <= 32);

        let mut buf_a = [_mm256_setzero_si256(); 32];
        let mut buf_b = [_mm256_setzero_si256(); 32];
        let two_inv_v = bc(two_inv_raw);

        let (start, end) = (leaf_range.start, leaf_range.end);
        let mut leaf_idx = start;
        while leaf_idx < end {
            let two = leaf_idx + 1 < end;
            for k in 0..n {
                buf_a[k] = if two {
                    ld2(column.add(offsets[k] + leaf_idx))
                } else {
                    ld1(column.add(offsets[k] + leaf_idx))
                };
            }
            let mut root_inv_lo = root_invs_raw[leaf_idx];
            let mut root_inv_hi = if two {
                root_invs_raw[leaf_idx + 1]
            } else {
                root_inv_lo
            };

            let mut src_is_a = true;
            for stage in 0..rounds {
                let num_existing = 1usize << stage;
                let block_len = n >> stage;
                let half = block_len / 2;
                // fused per-stage twiddles per half: rt2 = mont(mont(root_inv, hp[set]), two_inv)
                let mut rt2 = [_mm256_setzero_si256(); 16];
                for set_idx in 0..half {
                    let r_lo = super::mont_mul_scalar(root_inv_lo, hp_raw[set_idx]);
                    let r_hi = super::mont_mul_scalar(root_inv_hi, hp_raw[set_idx]);
                    rt2[set_idx] = bc2(
                        super::mont_mul_scalar(r_lo, two_inv_raw),
                        super::mont_mul_scalar(r_hi, two_inv_raw),
                    );
                }
                let (src, dst): (&[__m256i; 32], &mut [__m256i; 32]) = if src_is_a {
                    (&*(&buf_a as *const _), &mut *(&mut buf_b as *mut _))
                } else {
                    (&*(&buf_b as *const _), &mut *(&mut buf_a as *mut _))
                };
                for idx in 0..num_existing {
                    let base = idx * block_len;
                    let out_base = idx * half;
                    let linear_base = (idx | num_existing) * half;
                    for set_idx in 0..half {
                        let a = src[base + 2 * set_idx];
                        let b = src[base + 2 * set_idx + 1];
                        dst[out_base + set_idx] = mont_mul(add(a, b), two_inv_v);
                        dst[linear_base + set_idx] = mont_mul(sub(a, b), rt2[set_idx]);
                    }
                }
                src_is_a = !src_is_a;
                root_inv_lo = super::mont_mul_scalar(root_inv_lo, root_inv_lo);
                root_inv_hi = super::mont_mul_scalar(root_inv_hi, root_inv_hi);
            }

            let fin: &[__m256i; 32] = if src_is_a {
                &*(&buf_a as *const _)
            } else {
                &*(&buf_b as *const _)
            };
            for k in 0..n {
                if two {
                    st2(column.add(offsets[k] + leaf_idx), fin[k]);
                } else {
                    st1(column.add(offsets[k] + leaf_idx), fin[k]);
                }
            }
            leaf_idx += if two { 2 } else { 1 };
        }
    }

    /// ONE gathered leaf (`leaf.len()` = values per leaf, 2..=32, in the
    /// tree's leaf order) from evaluation to multilinear-coefficient form, in
    /// place: the per-leaf kernel of [`leaves_to_coeff_form`] over a
    /// contiguous buffer (identity offsets). Byte-identical to the scalar
    /// `evals_to_multilinear_coeffs`.
    pub fn leaf_to_coeff_form(
        leaf: &mut [BabyBearExt4],
        hp_raw: &[u32],
        two_inv: BabyBearField,
        root_inv_raw: u32,
    ) {
        const IDENTITY: [usize; 32] = {
            let mut a = [0usize; 32];
            let mut i = 0;
            while i < 32 {
                a[i] = i;
                i += 1;
            }
            a
        };
        let n = leaf.len();
        assert!(n >= 2 && n <= 32 && n.is_power_of_two());
        unsafe {
            fold_leaf_range(
                leaf.as_mut_ptr(),
                &IDENTITY[..n],
                hp_raw,
                two_inv.raw_u32_value(),
                &[root_inv_raw],
                0..1,
            );
        }
    }

    /// TWO gathered leaves, slot-interleaved (`pair[2k]` = slot `k` of the
    /// first leaf, `pair[2k + 1]` of the second; `pair.len() = 2 * values per
    /// leaf`, 2..=32 values), converted in place through the two-leaves-per-
    /// vector kernel. Byte-identical to `evals_to_multilinear_coeffs` per leaf.
    pub fn leaf_pair_to_coeff_form(
        pair: &mut [BabyBearExt4],
        hp_raw: &[u32],
        two_inv: BabyBearField,
        root_invs_raw: [u32; 2],
    ) {
        const STRIDE2: [usize; 32] = {
            let mut a = [0usize; 32];
            let mut i = 0;
            while i < 32 {
                a[i] = 2 * i;
                i += 1;
            }
            a
        };
        let n = pair.len() / 2;
        assert!(n >= 2 && n <= 32 && n.is_power_of_two() && pair.len() == 2 * n);
        unsafe {
            fold_leaf_range(
                pair.as_mut_ptr(),
                &STRIDE2[..n],
                hp_raw,
                two_inv.raw_u32_value(),
                &root_invs_raw,
                0..2,
            );
        }
    }

    /// FOUR gathered leaves, slot-major (`quad[4k + w]` = slot `k` of leaf
    /// `w`; `quad.len() = 4 * values per leaf`, 2..=32 values), converted in
    /// place as two vector pairs. Byte-identical to
    /// `evals_to_multilinear_coeffs` per leaf.
    pub fn leaf_quad_to_coeff_form(
        quad: &mut [BabyBearExt4],
        hp_raw: &[u32],
        two_inv: BabyBearField,
        root_invs_raw: [u32; 4],
    ) {
        const STRIDE4: [usize; 32] = {
            let mut a = [0usize; 32];
            let mut i = 0;
            while i < 32 {
                a[i] = 4 * i;
                i += 1;
            }
            a
        };
        let n = quad.len() / 4;
        assert!(n >= 2 && n <= 32 && n.is_power_of_two() && quad.len() == 4 * n);
        unsafe {
            fold_leaf_range(
                quad.as_mut_ptr(),
                &STRIDE4[..n],
                hp_raw,
                two_inv.raw_u32_value(),
                &root_invs_raw,
                0..4,
            );
        }
    }

    /// Serial coset conversion. Byte-identical to the scalar
    /// `ExtCoeffConvCtx::apply_serial`.
    pub fn leaves_to_coeff_form_serial(
        column: &mut [BabyBearExt4],
        offsets: &[usize],
        hp_raw: &[u32],
        two_inv: BabyBearField,
        root_invs_raw: &[u32],
    ) {
        unsafe {
            fold_leaf_range(
                column.as_mut_ptr(),
                offsets,
                hp_raw,
                two_inv.raw_u32_value(),
                root_invs_raw,
                0..root_invs_raw.len(),
            );
        }
    }

    /// Worker-parallel coset conversion (leaves chunked over the worker).
    /// Byte-identical to the scalar `ExtCoeffConvCtx::apply`.
    pub fn leaves_to_coeff_form(
        column: &mut [BabyBearExt4],
        offsets: &[usize],
        hp_raw: &[u32],
        two_inv: BabyBearField,
        root_invs_raw: &[u32],
        worker: &Worker,
    ) {
        let num_leaves = root_invs_raw.len();
        let base_addr = column.as_mut_ptr() as usize;
        let two_inv_raw = two_inv.raw_u32_value();
        worker.scope(num_leaves, |scope, geometry| {
            let (work, chunks) = (num_leaves, geometry.len());
            for thread_idx in 0..chunks {
                let (start, size) = balanced_chunk(work, chunks, thread_idx);
                spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                    fold_leaf_range(
                        base_addr as *mut BabyBearExt4,
                        offsets,
                        hp_raw,
                        two_inv_raw,
                        root_invs_raw,
                        start..start + size,
                    );
                });
            }
        });
    }

    /// Radix-4 fused ADD sweep (strides `s`, `2s`) over items.
    #[inline(always)]
    unsafe fn add_radix4_items(
        a: *mut BabyBearExt4,
        s: usize,
        item_range: core::ops::Range<usize>,
    ) {
        let (start, end) = (item_range.start, item_range.end);
        let core = |x0: __m256i, x1: __m256i, x2: __m256i, x3: __m256i| {
            // stride s: x1 += x0; x3 += x2. stride 2s: x2 += x0; x3 += x1'
            let n1 = add(x1, x0);
            let n3 = add(add(x3, x2), n1);
            let n2 = add(x2, x0);
            (n1, n2, n3)
        };
        if s == 1 {
            let mut t = start;
            while t + 1 < end {
                let j = 4 * t;
                let a01 = ld2(a.add(j));
                let a23 = ld2(a.add(j + 2));
                let b01 = ld2(a.add(j + 4));
                let b23 = ld2(a.add(j + 6));
                let x0 = lows(a01, b01);
                let (n1, n2, n3) = core(x0, highs(a01, b01), lows(a23, b23), highs(a23, b23));
                st2(a.add(j), lows(x0, n1));
                st2(a.add(j + 2), lows(n2, n3));
                st2(a.add(j + 4), highs(x0, n1));
                st2(a.add(j + 6), highs(n2, n3));
                t += 2;
            }
            if t < end {
                let j = 4 * t;
                let (n1, n2, n3) = core(
                    ld1(a.add(j)),
                    ld1(a.add(j + 1)),
                    ld1(a.add(j + 2)),
                    ld1(a.add(j + 3)),
                );
                st1(a.add(j + 1), n1);
                st1(a.add(j + 2), n2);
                st1(a.add(j + 3), n3);
            }
            return;
        }
        let mut t = start;
        let single = |t: usize| {
            let blk = t / s;
            let j = blk * (4 * s) + (t % s);
            let (n1, n2, n3) = core(
                ld1(a.add(j)),
                ld1(a.add(j + s)),
                ld1(a.add(j + 2 * s)),
                ld1(a.add(j + 3 * s)),
            );
            st1(a.add(j + s), n1);
            st1(a.add(j + 2 * s), n2);
            st1(a.add(j + 3 * s), n3);
        };
        if t < end && t % 2 == 1 {
            single(t);
            t += 1;
        }
        while t + 1 < end {
            let blk = t / s;
            let j = blk * (4 * s) + (t % s);
            let (n1, n2, n3) = core(
                ld2(a.add(j)),
                ld2(a.add(j + s)),
                ld2(a.add(j + 2 * s)),
                ld2(a.add(j + 3 * s)),
            );
            st2(a.add(j + s), n1);
            st2(a.add(j + 2 * s), n2);
            st2(a.add(j + 3 * s), n3);
            t += 2;
        }
        if t < end {
            single(t);
        }
    }

    /// Single ADD sweep (stride `s`) over items.
    #[inline(always)]
    unsafe fn add_single_items(
        a: *mut BabyBearExt4,
        s: usize,
        item_range: core::ops::Range<usize>,
    ) {
        let (start, end) = (item_range.start, item_range.end);
        if s == 1 {
            let mut t = start;
            while t + 1 < end {
                let j = 2 * t;
                let a01 = ld2(a.add(j));
                let b01 = ld2(a.add(j + 2));
                let x0 = lows(a01, b01);
                let n1 = add(highs(a01, b01), x0);
                st2(a.add(j), lows(x0, n1));
                st2(a.add(j + 2), highs(x0, n1));
                t += 2;
            }
            if t < end {
                let j = 2 * t;
                st1(a.add(j + 1), add(ld1(a.add(j + 1)), ld1(a.add(j))));
            }
            return;
        }
        let mut t = start;
        let single = |t: usize| {
            let blk = t / s;
            let j = blk * (2 * s) + (t % s);
            st1(a.add(j + s), add(ld1(a.add(j + s)), ld1(a.add(j))));
        };
        if t < end && t % 2 == 1 {
            single(t);
            t += 1;
        }
        while t + 1 < end {
            let blk = t / s;
            let j = blk * (2 * s) + (t % s);
            st2(a.add(j + s), add(ld2(a.add(j + s)), ld2(a.add(j))));
            t += 2;
        }
        if t < end {
            single(t);
        }
    }

    /// Worker-parallel `monomial coefficients -> hypercube evals` (the ADD
    /// Mobius transform, strides 1 -> n/2, radix-4 fused vector adds), all
    /// threads on one array. Byte-identical to
    /// `multivariate_coeffs_into_hypercube_evals` (natural LSB order).
    pub fn hypercube_evals_from_monomial_form(
        mut v: Vec<BabyBearExt4>,
        worker: &Worker,
    ) -> Vec<BabyBearExt4> {
        let n = v.len();
        let log_n = n.trailing_zeros();
        const PAR_THRESHOLD: usize = 1 << 12;
        let base_addr = v.as_mut_ptr() as usize;

        if n < PAR_THRESHOLD {
            unsafe {
                let p = v.as_mut_ptr();
                let mut s = 1usize;
                let mut left = log_n;
                while left >= 2 {
                    add_radix4_items(p, s, 0..n / 4);
                    s *= 4;
                    left -= 2;
                }
                if left == 1 {
                    add_single_items(p, s, 0..n / 2);
                }
            }
            return v;
        }

        let mut s = 1usize;
        let mut left = log_n;
        while left >= 2 {
            let cur_s = s;
            worker.scope(n / 4, |scope, geometry| {
                let (work, chunks) = (n / 4, geometry.len());
                for thread_idx in 0..chunks {
                    let (start, size) = balanced_chunk(work, chunks, thread_idx);
                    spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                        add_radix4_items(
                            base_addr as *mut BabyBearExt4,
                            cur_s,
                            start..start + size,
                        );
                    });
                }
            });
            s *= 4;
            left -= 2;
        }
        if left == 1 {
            let cur_s = s;
            worker.scope(n / 2, |scope, geometry| {
                let (work, chunks) = (n / 2, geometry.len());
                for thread_idx in 0..chunks {
                    let (start, size) = balanced_chunk(work, chunks, thread_idx);
                    spawn_chunk(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                        add_single_items(
                            base_addr as *mut BabyBearExt4,
                            cur_s,
                            start..start + size,
                        );
                    });
                }
            });
        }
        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::twiddles::precompute_all_twiddles_for_fft_serial;
    use field::{FieldExtension, PrimeField, Rand};
    use std::alloc::Global;

    /// Every Ext4 AVX2 kernel must equal its scalar reference exactly, across
    /// sizes covering the tiny fallback, the serial pairing paths (odd worker
    /// chunks included) and the parallel-within-task paths.
    #[test]
    fn ext4_avx2_kernels_match_reference() {
        use field::baby_bear::ext4::BabyBearExt4;
        for num_threads in [3usize, 4] {
            let worker = worker::Worker::new_with_num_threads(num_threads);
            // 2^17..2^21 exercise the radix-16 global phase of the blocked
            // kernel with every leftover class
            for log_n in [
                3u32, 4, 5, 6, 7, 8, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
            ] {
                let n = 1usize << log_n;
                let mut rng = rand::rng();
                let input: Vec<BabyBearExt4> = (0..n)
                    .map(|_| BabyBearExt4::random_element(&mut rng))
                    .collect();
                let tw: Vec<BabyBearField, Global> =
                    precompute_all_twiddles_for_fft_serial::<BabyBearField, Global, false>(n);
                let tw_inv: Vec<BabyBearField, Global> =
                    precompute_all_twiddles_for_fft_serial::<BabyBearField, Global, true>(n);
                let ext = Avx2TwiddleExt::build(&tw, n);
                let ext_inv = Avx2TwiddleExt::build(&tw_inv, n);
                let offset =
                    crate::field_utils::domain_generator_for_size::<BabyBearField>((n * 2) as u64);

                for off in [offset, BabyBearField::ONE] {
                    let expected = crate::lde_coset_natural_seq_fused(&input, off, &tw);
                    let got = ext4::lde_coset(&input, off, &tw, &ext);
                    assert_eq!(got, expected, "ext4 serial LDE diverged at log_n={log_n}");
                    let got = ext4::lde_coset_parallel(&input, off, &tw, &ext, &worker);
                    assert_eq!(got, expected, "ext4 parallel LDE diverged at log_n={log_n}");
                }

                let mut expected = input.clone();
                crate::naive::cache_friendly_ntt_natural_to_bitreversed(
                    &mut expected,
                    log_n,
                    &tw_inv[..(n / 2).max(1)],
                );
                let size_inv = BabyBearField::from_u32_unchecked(n as u32)
                    .inverse()
                    .unwrap();
                for el in expected.iter_mut() {
                    el.mul_assign_by_base(&size_inv);
                }
                crate::utils::bitreverse_enumeration_inplace(&mut expected);
                let got =
                    ext4::monomial_form_from_main_domain(input.clone(), &tw_inv, &ext_inv, &worker);
                assert_eq!(got, expected, "ext4 inverse diverged at log_n={log_n}");

                let mut expected = input.clone();
                {
                    for [a, b] in expected.as_chunks_mut::<2>().0.iter_mut() {
                        b.add_assign(&a);
                    }
                    let mut stride = 2usize;
                    for _round in 1..log_n {
                        let mut i = 0usize;
                        while i < n {
                            for _ in 0..stride {
                                let lhs = expected[i];
                                expected[i + stride].add_assign(&lhs);
                                i += 1;
                            }
                            i += stride;
                        }
                        stride *= 2;
                    }
                }
                let got = ext4::hypercube_evals_from_monomial_form(input.clone(), &worker);
                assert_eq!(got, expected, "ext4 hc-evals diverged at log_n={log_n}");
            }
        }
    }

    /// The blocked worker-parallel base-field LDE must equal the serial
    /// reference exactly (sizes at and above the 2^16 blocked threshold, odd
    /// thread counts for uneven chunking).
    #[test]
    fn avx2_parallel_lde_matches_reference() {
        for num_threads in [3usize, 8] {
            let worker = worker::Worker::new_with_num_threads(num_threads);
            // 2^16..2^22 covers every phase-B leftover class (0..3 levels)
            // and the one-/two-pass radix-16 shapes
            for log_n in [16u32, 17, 18, 19, 20, 21, 22] {
                let n = 1usize << log_n;
                let mut rng = rand::rng();
                let input: Vec<BabyBearField> = (0..n)
                    .map(|_| BabyBearField::random_element(&mut rng))
                    .collect();
                let tw: Vec<BabyBearField, Global> =
                    precompute_all_twiddles_for_fft_serial::<BabyBearField, Global, false>(n);
                let offset =
                    crate::field_utils::domain_generator_for_size::<BabyBearField>((n * 2) as u64);
                let ext = Avx2TwiddleExt::build(&tw, n);
                for off in [offset, BabyBearField::ONE] {
                    let expected = crate::lde_coset_natural_seq_fused(&input, off, &tw);
                    let got = lde_coset_avx2_parallel(&input, off, &tw, &ext, &worker);
                    assert_eq!(got, expected, "AVX2 parallel LDE diverged at log_n={log_n}");
                }
            }
        }
    }

    /// The AVX2 base-field pipeline must equal `lde_coset_natural_seq_fused`
    /// exactly, across ppg-parity classes, both offset branches, and the
    /// tiny-size fallback path (log_n < 5 degrades to the scalar reference).
    #[test]
    fn avx2_lde_matches_reference() {
        for log_n in [1u32, 2, 3, 4, 5, 6, 7, 8, 11, 14, 16] {
            let n = 1usize << log_n;
            let mut rng = rand::rng();
            let input: Vec<BabyBearField> = (0..n)
                .map(|_| BabyBearField::random_element(&mut rng))
                .collect();
            let tw: Vec<BabyBearField, Global> =
                precompute_all_twiddles_for_fft_serial::<BabyBearField, Global, false>(n);
            let offset =
                crate::field_utils::domain_generator_for_size::<BabyBearField>((n * 2) as u64);
            let ext = Avx2TwiddleExt::build(&tw, n);

            for off in [offset, BabyBearField::ONE] {
                let expected = crate::lde_coset_natural_seq_fused(&input, off, &tw);
                let got = lde_coset_avx2(&input, off, &tw, &ext);
                assert_eq!(got, expected, "AVX2 pipeline diverged at log_n={log_n}");
            }
        }
    }
}
