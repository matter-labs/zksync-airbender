//! NEON-vectorized BabyBear flat LDE-coset kernel (aarch64) — the production
//! serial coset pipeline of the BabyBear work-stealing backend on Apple/ARM
//! hosts.
//!
//! BabyBear is `p = 2^31 - 2^27 + 1` in standard 32-bit Montgomery form
//! (`R = 2^32`), canonical at rest: four elements per NEON vector, Montgomery
//! product via two `umull` pairs + `uzp2` high-word extraction + one `vmin`
//! conditional subtract. Every op returns canonical values, so the kernel is
//! BYTE-IDENTICAL to `lde_coset_natural_seq_fused` (asserted by the tests).
//!
//! Stage plan of the GS DIT NTT (bit-reversed input → natural output):
//! `ppg == 1` and `ppg == 2` run as dedicated in-register shuffle passes
//! (`uzp`/`zip` on 32-/64-bit lanes) — no scalar fallback; `ppg >= 4` stages
//! run as radix-4 FUSED passes (two butterfly levels per sweep, broadcast
//! twiddles, same twiddle indexing as `higher_radix`); the last multiplying
//! level is fused with the final twiddle-free level.
//!
//! Partial (lazy) reduction was evaluated and rejected: `2p ≈ 2^31.9` leaves
//! no headroom in 32-bit lanes (lazy adds wrap, lazy×lazy muls exceed `2p`),
//! and the measured all-cond-subs-stripped ceiling is ~1.3x on the NTT part
//! only — unreachable without dropping to 2-wide 64-bit lanes.

#![cfg(target_arch = "aarch64")]

use field::baby_bear::base::BabyBearField;
use field::{Field, PrimeField};

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

mod neon {
    use super::{K, P};
    use core::arch::aarch64::*;

    #[inline(always)]
    unsafe fn pv() -> uint32x4_t {
        vdupq_n_u32(P)
    }

    #[inline(always)]
    pub unsafe fn mont_mul(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
        let lo = vmulq_u32(a, b);
        let prod_l = vmull_u32(vget_low_u32(a), vget_low_u32(b));
        let prod_h = vmull_high_u32(a, b);
        let m = vmulq_u32(lo, vdupq_n_u32(K));
        let mp_l = vmull_u32(vget_low_u32(m), vget_low_u32(pv()));
        let mp_h = vmull_high_u32(m, pv());
        let t_l = vaddq_u64(prod_l, mp_l);
        let t_h = vaddq_u64(prod_h, mp_h);
        let r = vuzp2q_u32(vreinterpretq_u32_u64(t_l), vreinterpretq_u32_u64(t_h));
        let rs = vsubq_u32(r, pv());
        vminq_u32(r, rs)
    }

    #[inline(always)]
    pub unsafe fn add(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
        let s = vaddq_u32(a, b);
        vminq_u32(s, vsubq_u32(s, pv()))
    }

    #[inline(always)]
    pub unsafe fn sub(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
        let d = vsubq_u32(a, b);
        vminq_u32(d, vaddq_u32(d, pv()))
    }

    #[inline(always)]
    unsafe fn butterfly(u: uint32x4_t, v: uint32x4_t, s: uint32x4_t) -> (uint32x4_t, uint32x4_t) {
        (add(u, v), mont_mul(sub(u, v), s))
    }

    #[inline(always)]
    unsafe fn pass_ppg1(a: *mut u32, n: usize, tw: *const u32) {
        let mut j = 0usize;
        while j < n {
            let v0 = vld1q_u32(a.add(j));
            let v1 = vld1q_u32(a.add(j + 4));
            let u = vuzp1q_u32(v0, v1);
            let v = vuzp2q_u32(v0, v1);
            let s = vld1q_u32(tw.add(j >> 1));
            let (na, nb) = butterfly(u, v, s);
            vst1q_u32(a.add(j), vzip1q_u32(na, nb));
            vst1q_u32(a.add(j + 4), vzip2q_u32(na, nb));
            j += 8;
        }
    }

    #[inline(always)]
    unsafe fn pass_ppg2(a: *mut u32, n: usize, tw: *const u32) {
        let mut j = 0usize;
        while j < n {
            let v0 = vreinterpretq_u64_u32(vld1q_u32(a.add(j)));
            let v1 = vreinterpretq_u64_u32(vld1q_u32(a.add(j + 4)));
            let u = vreinterpretq_u32_u64(vuzp1q_u64(v0, v1));
            let v = vreinterpretq_u32_u64(vuzp2q_u64(v0, v1));
            let d = vld1_u32(tw.add(j >> 2));
            let t = vcombine_u32(d, d);
            let s = vzip1q_u32(t, t);
            let (na, nb) = butterfly(u, v, s);
            let na64 = vreinterpretq_u64_u32(na);
            let nb64 = vreinterpretq_u64_u32(nb);
            vst1q_u32(a.add(j), vreinterpretq_u32_u64(vzip1q_u64(na64, nb64)));
            vst1q_u32(a.add(j + 4), vreinterpretq_u32_u64(vzip2q_u64(na64, nb64)));
            j += 8;
        }
    }

    /// Montgomery REDC of 64-bit lane accumulators (`t < R*p`), canonical out.
    #[inline(always)]
    pub unsafe fn redc64(t_l: uint64x2_t, t_h: uint64x2_t) -> uint32x4_t {
        let lo32 = vuzp1q_u32(vreinterpretq_u32_u64(t_l), vreinterpretq_u32_u64(t_h));
        let m = vmulq_u32(lo32, vdupq_n_u32(K));
        let mp_l = vmull_u32(vget_low_u32(m), vget_low_u32(pv()));
        let mp_h = vmull_high_u32(m, pv());
        let s_l = vaddq_u64(t_l, mp_l);
        let s_h = vaddq_u64(t_h, mp_h);
        let r = vuzp2q_u32(vreinterpretq_u32_u64(s_l), vreinterpretq_u32_u64(s_h));
        let rs = vsubq_u32(r, pv());
        vminq_u32(r, rs)
    }

    #[inline(always)]
    pub unsafe fn widening_mul(a: uint32x4_t, b: uint32x4_t) -> (uint64x2_t, uint64x2_t) {
        (
            vmull_u32(vget_low_u32(a), vget_low_u32(b)),
            vmull_high_u32(a, b),
        )
    }

    /// Radix-4 pass with U64 ACCUMULATION (measured ~1.1x over the plain
    /// pass): the odd outputs are single REDCs of 64-bit product sums —
    /// `X1 = REDC(D01*s_a + D23*s_b)` and, via the precomputed COMBINED
    /// twiddles `s_ao = mont(tw[2k], tw[k])`, `s_bo = mont(tw[2k+1], tw[k])`,
    /// `X3 = REDC(D01*s_ao - D23*s_bo + p*s_bo)` — no chained multiply.
    /// Accumulators < 2p^2 < R*p, so REDC stays exact; outputs canonical =>
    /// byte-identical to the two-level reference.
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
            let s_a = vdupq_n_u32(*tw.add(2 * k2));
            let s_b = vdupq_n_u32(*tw.add(2 * k2 + 1));
            let s_o = vdupq_n_u32(*tw.add(k2));
            let s_ao = vdupq_n_u32(*tw_ao.add(k2));
            let s_bo = vdupq_n_u32(*tw_bo.add(k2));
            let bias = vdupq_n_u64((P as u64) * (*tw_bo.add(k2) as u64));
            let base = k2 * ppg * 4;
            let mut j = base;
            while j < base + ppg {
                let x0 = vld1q_u32(a.add(j));
                let x1 = vld1q_u32(a.add(j + ppg));
                let x2 = vld1q_u32(a.add(j + 2 * ppg));
                let x3 = vld1q_u32(a.add(j + 3 * ppg));

                let y0 = add(x0, x1);
                let y2 = add(x2, x3);
                let z0 = add(y0, y2);
                let z2 = mont_mul(sub(y0, y2), s_o);

                let d01 = sub(x0, x1);
                let d23 = sub(x2, x3);
                let (p1l, p1h) = widening_mul(d01, s_a);
                let (p2l, p2h) = widening_mul(d23, s_b);
                let z1 = redc64(vaddq_u64(p1l, p2l), vaddq_u64(p1h, p2h));
                let (p3l, p3h) = widening_mul(d01, s_ao);
                let (p4l, p4h) = widening_mul(d23, s_bo);
                let z3 = redc64(
                    vsubq_u64(vaddq_u64(p3l, bias), p4l),
                    vsubq_u64(vaddq_u64(p3h, bias), p4h),
                );

                vst1q_u32(a.add(j), z0);
                vst1q_u32(a.add(j + ppg), z1);
                vst1q_u32(a.add(j + 2 * ppg), z2);
                vst1q_u32(a.add(j + 3 * ppg), z3);
                j += 4;
            }
        }
    }

    #[inline(always)]
    unsafe fn tail_two_groups(a: *mut u32, n: usize, tw: *const u32) {
        let q = n / 4;
        let s_a = vdupq_n_u32(*tw);
        let s_b = vdupq_n_u32(*tw.add(1));
        let mut j = 0usize;
        while j < q {
            let x0 = vld1q_u32(a.add(j));
            let x1 = vld1q_u32(a.add(j + q));
            let x2 = vld1q_u32(a.add(j + 2 * q));
            let x3 = vld1q_u32(a.add(j + 3 * q));
            let (y0, y1) = butterfly(x0, x1, s_a);
            let (y2, y3) = butterfly(x2, x3, s_b);
            vst1q_u32(a.add(j), add(y0, y2));
            vst1q_u32(a.add(j + 2 * q), sub(y0, y2));
            vst1q_u32(a.add(j + q), add(y1, y3));
            vst1q_u32(a.add(j + 3 * q), sub(y1, y3));
            j += 4;
        }
    }

    #[inline(always)]
    unsafe fn tail_final(a: *mut u32, n: usize) {
        let half = n / 2;
        let mut j = 0usize;
        while j < half {
            let u = vld1q_u32(a.add(j));
            let v = vld1q_u32(a.add(j + half));
            vst1q_u32(a.add(j), add(u, v));
            vst1q_u32(a.add(j + half), sub(u, v));
            j += 4;
        }
    }

    /// Fully-NEON GS DIT NTT on raw canonical values, `n >= 16`, with
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
        debug_assert!(n >= 16);
        debug_assert!(n < 32 || (tw_ao.len() >= n / 16 && tw_bo.len() >= n / 16));
        let p = a.as_mut_ptr();
        let t = tw.as_ptr();
        pass_ppg1(p, n, t);
        pass_ppg2(p, n, t);
        let mut ppg = 4usize;
        let mut num_groups = n / 8;
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
/// `k < n/16` (the largest outer-group range; smaller passes use a prefix).
/// Depends only on the (fixed per prover run) twiddle table — build once per
/// batched backend call and share across all its coset tasks.
pub struct NeonTwiddleExt {
    ao: Vec<u32>,
    bo: Vec<u32>,
}

impl NeonTwiddleExt {
    /// `twiddles` is the standard bit-reversed table (>= n/2 entries), `n` the
    /// (largest) transform size the tables must serve. Sized `n/4`: the Ext4
    /// kernels fuse from `ppg == 1`, where the outer-group index reaches
    /// `n/4` (the base-field kernel only reads the `n/16` prefix). Transforms
    /// below 8 elements have no fused pass, so the tables stay empty.
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

    /// [`Self::build`] with the fill chunked over the worker: the entries
    /// are independent functions of `k`, so the (up to `n/4`-entry,
    /// coset-scale) tables fan out across the pool instead of running as a
    /// serial ~`n/2`-multiply prologue; small tables run inline. Writes
    /// first-touch into the vectors' spare capacity (no pre-fill).
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
                worker::Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
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

/// Serial LDE coset, fully NEON: scaled copy (vector muls, split-power
/// factors), scalar bit-reversal, NEON u64-accumulation radix-4 NTT.
/// Byte-identical drop-in for `lde_coset_natural_seq_fused` on BabyBear;
/// degrades to the scalar reference below 16 elements (so EVERY poly size is
/// supported). `ext` must be built for a transform size >= `input.len()`.
pub fn lde_coset_neon(
    input: &[BabyBearField],
    offset: BabyBearField,
    twiddles: &[BabyBearField],
    ext: &NeonTwiddleExt,
) -> Vec<BabyBearField> {
    let n = input.len();
    if n < 16 {
        return crate::lde_coset_natural_seq_fused(input, offset, twiddles);
    }
    let log_n = n.trailing_zeros();

    // repr(transparent) reinterpretations — raw canonical Montgomery values.
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
            use core::arch::aarch64::*;
            let lo_len = sp.mask + 1;
            let src = input_raw.as_ptr();
            let dst = v.as_mut_ptr();
            let mut i = 0usize;
            while i < n {
                let hi = vdupq_n_u32(sp.hi[i >> sp.h]);
                let block_end = i + lo_len;
                let mut j = i;
                // lo_len >= 4 for n >= 16
                while j < block_end {
                    let lo = vld1q_u32(sp.lo.as_ptr().add(j - i));
                    let f = neon::mont_mul(lo, hi);
                    let x = vld1q_u32(src.add(j));
                    vst1q_u32(dst.add(j), neon::mont_mul(x, f));
                    j += 4;
                }
                i = block_end;
            }
        }
    } else {
        v.copy_from_slice(input_raw);
    }

    crate::utils::bitreverse_enumeration_inplace(&mut v);

    unsafe {
        neon::ntt_bitrev_to_natural(&mut v, log_n, &tw_raw[..n / 2], &ext.ao, &ext.bo);
    }

    // SAFETY: repr(transparent), all values canonical.
    unsafe { core::mem::transmute::<Vec<u32>, Vec<BabyBearField>>(v) }
}

// keep the scalar helper referenced (power tables use field ops only)
const _: fn(u32, u32) -> u32 = mont_mul_scalar;

/// NEON kernels for `BabyBearExt4` polynomials with BASE-field twiddles: one
/// extension element is exactly one 16-B-aligned `uint32x4_t`, and every
/// butterfly is component-wise (vector add/sub, `mul_assign_by_base` = 4-lane
/// Montgomery mul by a broadcast scalar) — so there are NO lane-shuffle
/// special cases; every stage down to element-distance 1 is a whole-vector
/// op. Radix-4 fused passes reuse the u64-accumulation trick and the SAME
/// [`NeonTwiddleExt`] combined tables (`mont` is commutative, so the forward
/// GS and inverse CT fusions need identical products). All kernels are
/// byte-identical to their scalar references and degrade to them below 16
/// elements.
pub mod ext4 {
    use super::neon::{add, mont_mul, redc64, sub, widening_mul};
    use super::{NeonTwiddleExt, SplitPowersRaw, P};
    use core::arch::aarch64::*;
    use field::baby_bear::base::BabyBearField;
    use field::baby_bear::ext4::BabyBearExt4;
    use field::{Field, FieldExtension, PrimeField};
    use worker::Worker;

    #[inline(always)]
    unsafe fn ld(p: *const BabyBearExt4) -> uint32x4_t {
        vld1q_u32(p as *const u32)
    }
    #[inline(always)]
    unsafe fn st(p: *mut BabyBearExt4, v: uint32x4_t) {
        vst1q_u32(p as *mut u32, v)
    }

    /// FORWARD (GS, bit-reversed -> natural) radix-4 fused pass over element
    /// indices, u64 accumulation on the odd outputs; works for ANY `ppg >= 1`.
    #[inline(always)]
    unsafe fn fwd_radix4_items(
        a: *mut BabyBearExt4,
        ppg: usize,
        tw: *const u32,
        tw_ao: *const u32,
        tw_bo: *const u32,
        item_range: core::ops::Range<usize>,
    ) {
        for t in item_range {
            let k2 = t / ppg;
            let j = k2 * (ppg * 4) + (t % ppg);
            let s_a = vdupq_n_u32(*tw.add(2 * k2));
            let s_b = vdupq_n_u32(*tw.add(2 * k2 + 1));
            let s_o = vdupq_n_u32(*tw.add(k2));
            let s_ao = vdupq_n_u32(*tw_ao.add(k2));
            let s_bo = vdupq_n_u32(*tw_bo.add(k2));
            let bias = vdupq_n_u64((P as u64) * (*tw_bo.add(k2) as u64));

            let x0 = ld(a.add(j));
            let x1 = ld(a.add(j + ppg));
            let x2 = ld(a.add(j + 2 * ppg));
            let x3 = ld(a.add(j + 3 * ppg));

            let y0 = add(x0, x1);
            let y2 = add(x2, x3);
            let z0 = add(y0, y2);
            let z2 = mont_mul(sub(y0, y2), s_o);

            let d01 = sub(x0, x1);
            let d23 = sub(x2, x3);
            let (p1l, p1h) = widening_mul(d01, s_a);
            let (p2l, p2h) = widening_mul(d23, s_b);
            let z1 = redc64(vaddq_u64(p1l, p2l), vaddq_u64(p1h, p2h));
            let (p3l, p3h) = widening_mul(d01, s_ao);
            let (p4l, p4h) = widening_mul(d23, s_bo);
            let z3 = redc64(
                vsubq_u64(vaddq_u64(p3l, bias), p4l),
                vsubq_u64(vaddq_u64(p3h, bias), p4h),
            );

            st(a.add(j), z0);
            st(a.add(j + ppg), z1);
            st(a.add(j + 2 * ppg), z2);
            st(a.add(j + 3 * ppg), z3);
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
        let s_a = vdupq_n_u32(*tw);
        let s_b = vdupq_n_u32(*tw.add(1));
        for j in jr {
            let x0 = ld(a.add(j));
            let x1 = ld(a.add(j + q));
            let x2 = ld(a.add(j + 2 * q));
            let x3 = ld(a.add(j + 3 * q));
            let y0 = add(x0, x1);
            let y1 = mont_mul(sub(x0, x1), s_a);
            let y2 = add(x2, x3);
            let y3 = mont_mul(sub(x2, x3), s_b);
            st(a.add(j), add(y0, y2));
            st(a.add(j + 2 * q), sub(y0, y2));
            st(a.add(j + q), add(y1, y3));
            st(a.add(j + 3 * q), sub(y1, y3));
        }
    }

    #[inline(always)]
    unsafe fn fwd_tail_final(a: *mut BabyBearExt4, n: usize, jr: core::ops::Range<usize>) {
        let half = n / 2;
        for j in jr {
            let u = ld(a.add(j));
            let v = ld(a.add(j + half));
            st(a.add(j), add(u, v));
            st(a.add(j + half), sub(u, v));
        }
    }

    /// Serial forward NTT (bit-reversed -> natural), byte-identical to
    /// `serial_ct_ntt_bitreversed_to_natural` over Ext4.
    pub unsafe fn ntt_fwd(a: &mut [BabyBearExt4], tw_raw: &[u32], ext: &NeonTwiddleExt) {
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

    /// Serial LDE coset over Ext4 — drop-in for `lde_coset_natural_seq_fused`
    /// (byte-identical); sizes below 16 degrade to it.
    pub fn lde_coset(
        input: &[BabyBearExt4],
        offset: BabyBearField,
        twiddles: &[BabyBearField],
        ext: &NeonTwiddleExt,
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

    /// [`lde_coset`] writing into a caller-provided buffer (e.g. one coset's
    /// chunk of a contiguous LDE codeword). `out` is WRITE-FIRST: every
    /// element is overwritten by the scaled-copy pass before any read, so it
    /// may be freshly allocated uninitialized memory.
    pub fn lde_coset_into(
        input: &[BabyBearExt4],
        offset: BabyBearField,
        twiddles: &[BabyBearField],
        ext: &NeonTwiddleExt,
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
                let src = input.as_ptr();
                let dst = out.as_mut_ptr();
                for i in 0..n {
                    let f =
                        vdupq_n_u32(super::mont_mul_scalar(sp.lo[i & sp.mask], sp.hi[i >> sp.h]));
                    st(dst.add(i), mont_mul(ld(src.add(i)), f));
                }
            }
        } else {
            out.copy_from_slice(input);
        }
        crate::utils::bitreverse_enumeration_inplace(out);
        unsafe {
            ntt_fwd(out, &tw_raw[..n / 2], ext);
        }
    }

    /// Worker-PARALLEL LDE coset over Ext4: every pass (scaled copy, bit
    /// reversal, each fused NTT sweep) runs worker-wide with a barrier between
    /// passes — the "all threads on one coset" mode. Byte-identical to the
    /// serial pipeline; falls back to it below 2^12 elements.
    pub fn lde_coset_parallel(
        input: &[BabyBearExt4],
        offset: BabyBearField,
        twiddles: &[BabyBearField],
        ext: &NeonTwiddleExt,
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

    /// [`lde_coset_parallel`] writing into a caller-provided buffer (e.g. one
    /// coset's chunk of a contiguous LDE codeword). `out` is WRITE-FIRST:
    /// every element is overwritten by the scaled-copy pass before any read,
    /// so it may be freshly allocated uninitialized memory.
    pub fn lde_coset_parallel_into(
        input: &[BabyBearExt4],
        offset: BabyBearField,
        twiddles: &[BabyBearField],
        ext: &NeonTwiddleExt,
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
                for thread_idx in 0..geometry.len() {
                    let start = geometry.get_chunk_start_pos(thread_idx);
                    let size = geometry.get_chunk_size(thread_idx);
                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                        let src = src_addr as *const BabyBearExt4;
                        let dst = dst_addr as *mut BabyBearExt4;
                        for i in start..(start + size) {
                            let f = vdupq_n_u32(super::mont_mul_scalar(
                                sp_ref.lo[i & sp_ref.mask],
                                sp_ref.hi[i >> sp_ref.h],
                            ));
                            st(dst.add(i), mont_mul(ld(src.add(i)), f));
                        }
                    });
                }
            });
        } else {
            worker.scope(n, |scope, geometry| {
                for thread_idx in 0..geometry.len() {
                    let start = geometry.get_chunk_start_pos(thread_idx);
                    let size = geometry.get_chunk_size(thread_idx);
                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                        let src = src_addr as *const BabyBearExt4;
                        let dst = dst_addr as *mut BabyBearExt4;
                        core::ptr::copy_nonoverlapping(src.add(start), dst.add(start), size);
                    });
                }
            });
        }

        crate::utils::parallel_bitreverse_enumeration_inplace(out, worker);

        // parallel forward NTT: one worker scope per fused pass
        let tw = &tw_raw[..n / 2];
        let base_addr = out.as_mut_ptr() as usize;
        let mut ppg = 1usize;
        let mut num_groups = n / 2;
        while num_groups >= 4 {
            let items = (num_groups / 2) * ppg;
            let cur_ppg = ppg;
            worker.scope(items, |scope, geometry| {
                for thread_idx in 0..geometry.len() {
                    let start = geometry.get_chunk_start_pos(thread_idx);
                    let size = geometry.get_chunk_size(thread_idx);
                    let (ao, bo) = (ext.ao.as_ptr() as usize, ext.bo.as_ptr() as usize);
                    let tw_addr = tw.as_ptr() as usize;
                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                        fwd_radix4_items(
                            base_addr as *mut BabyBearExt4,
                            cur_ppg,
                            tw_addr as *const u32,
                            ao as *const u32,
                            bo as *const u32,
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
                    for thread_idx in 0..geometry.len() {
                        let start = geometry.get_chunk_start_pos(thread_idx);
                        let size = geometry.get_chunk_size(thread_idx);
                        let tw_addr = tw.as_ptr() as usize;
                        Worker::smart_spawn(
                            scope,
                            thread_idx == geometry.len() - 1,
                            move |_| unsafe {
                                fwd_tail_two_groups(
                                    base_addr as *mut BabyBearExt4,
                                    n,
                                    tw_addr as *const u32,
                                    start..start + size,
                                );
                            },
                        );
                    }
                });
            }
            1 => {
                worker.scope(n / 2, |scope, geometry| {
                    for thread_idx in 0..geometry.len() {
                        let start = geometry.get_chunk_start_pos(thread_idx);
                        let size = geometry.get_chunk_size(thread_idx);
                        Worker::smart_spawn(
                            scope,
                            thread_idx == geometry.len() - 1,
                            move |_| unsafe {
                                fwd_tail_final(
                                    base_addr as *mut BabyBearExt4,
                                    n,
                                    start..start + size,
                                );
                            },
                        );
                    }
                });
            }
            _ => unreachable!(),
        }
    }

    /// INVERSE-direction (CT, natural -> bit-reversed) radix-4 fused pass with
    /// u64 accumulation — the same combined tables serve (`mont` commutes):
    /// per outer group `k` (twiddle `s`) and inner groups `2k`/`2k+1`
    /// (`s_a`/`s_b`):
    ///   `m1 = REDC64(x1*s_a + x3*ao[k])`  (= `(x1 + x3*s)*s_a`)
    ///   `m2 = REDC64(x1*s_b - x3*bo[k] + p*bo[k])`  (= `(x1 - x3*s)*s_b`)
    ///   `t2 = x2*s`; outputs `x0+t2 ± m1`-style CT combinations.
    #[inline(always)]
    unsafe fn inv_radix4_items(
        a: *mut BabyBearExt4,
        half_d: usize, // distance of the SECOND stage = d/2
        tw: *const u32,
        tw_ao: *const u32,
        tw_bo: *const u32,
        item_range: core::ops::Range<usize>,
    ) {
        for t in item_range {
            let k = t / half_d;
            let j = k * (half_d * 4) + (t % half_d);
            let s = vdupq_n_u32(*tw.add(k));
            let s_a = vdupq_n_u32(*tw.add(2 * k));
            let s_b = vdupq_n_u32(*tw.add(2 * k + 1));
            let s_ao = vdupq_n_u32(*tw_ao.add(k));
            let s_bo = vdupq_n_u32(*tw_bo.add(k));
            let bias = vdupq_n_u64((P as u64) * (*tw_bo.add(k) as u64));

            let x0 = ld(a.add(j));
            let x1 = ld(a.add(j + half_d));
            let x2 = ld(a.add(j + 2 * half_d));
            let x3 = ld(a.add(j + 3 * half_d));

            // stage d (distance 2*half_d, twiddle s): t2 = x2*s, t3 = x3*s
            //   y0 = x0 + t2; y2 = x0 - t2; y1 = x1 + t3; y3 = x1 - t3
            // stage d/2 (twiddles s_a on (y0,y1), s_b on (y2,y3)):
            //   z0 = y0 + y1*s_a; z1 = y0 - y1*s_a
            //   z2 = y2 + y3*s_b; z3 = y2 - y3*s_b
            let t2 = mont_mul(x2, s);
            let y0 = add(x0, t2);
            let y2 = sub(x0, t2);

            let (p1l, p1h) = widening_mul(x1, s_a);
            let (p2l, p2h) = widening_mul(x3, s_ao);
            let m1 = redc64(vaddq_u64(p1l, p2l), vaddq_u64(p1h, p2h));
            let (p3l, p3h) = widening_mul(x1, s_b);
            let (p4l, p4h) = widening_mul(x3, s_bo);
            let m2 = redc64(
                vsubq_u64(vaddq_u64(p3l, bias), p4l),
                vsubq_u64(vaddq_u64(p3h, bias), p4h),
            );

            st(a.add(j), add(y0, m1));
            st(a.add(j + half_d), sub(y0, m1));
            st(a.add(j + 2 * half_d), add(y2, m2));
            st(a.add(j + 3 * half_d), sub(y2, m2));
        }
    }

    /// First inverse stage (omega = 1) fused with the second (distance n/4,
    /// twiddles tw[0], tw[1]): the head counterpart of the forward tail.
    #[inline(always)]
    unsafe fn inv_head_two_stages(
        a: *mut BabyBearExt4,
        n: usize,
        tw: *const u32,
        jr: core::ops::Range<usize>,
    ) {
        let q = n / 4;
        let s_a = vdupq_n_u32(*tw);
        let s_b = vdupq_n_u32(*tw.add(1));
        for j in jr {
            let x0 = ld(a.add(j));
            let x1 = ld(a.add(j + q));
            let x2 = ld(a.add(j + 2 * q));
            let x3 = ld(a.add(j + 3 * q));
            // stage n/2 (s = 1): y0 = x0 + x2; y2 = x0 - x2; y1 = x1 + x3; y3 = x1 - x3
            let y0 = add(x0, x2);
            let y2 = sub(x0, x2);
            let y1 = add(x1, x3);
            let y3 = sub(x1, x3);
            // stage n/4: z0 = y0 + y1*s_a; z1 = y0 - y1*s_a; z2 = y2 + y3*s_b; z3 = y2 - y3*s_b
            let t1 = mont_mul(y1, s_a);
            let t3 = mont_mul(y3, s_b);
            st(a.add(j), add(y0, t1));
            st(a.add(j + q), sub(y0, t1));
            st(a.add(j + 2 * q), add(y2, t3));
            st(a.add(j + 3 * q), sub(y2, t3));
        }
    }

    /// First inverse stage alone (omega = 1, distance n/2).
    #[inline(always)]
    unsafe fn inv_head_single(a: *mut BabyBearExt4, n: usize, jr: core::ops::Range<usize>) {
        let half = n / 2;
        for j in jr {
            let u = ld(a.add(j));
            let v = ld(a.add(j + half));
            st(a.add(j), add(u, v));
            st(a.add(j + half), sub(u, v));
        }
    }

    /// Worker-parallel `main-domain evals -> monomial coefficients` for the
    /// O(1) batched Ext4 poly: parallel inverse NTT (natural -> bit-reversed,
    /// CT direction, radix-4 fused + u64-acc), parallel `1/N` scaling,
    /// parallel bit-reversal — ALL threads work on the single transform.
    /// `inv_ext` must be built from the INVERSE twiddle table. Byte-identical
    /// to `cache_friendly_ntt_natural_to_bitreversed` + scale + bitrev; sizes
    /// below 2^12 run the serial reference.
    pub fn monomial_form_from_main_domain(
        mut v: Vec<BabyBearExt4>,
        inverse_twiddles: &[BabyBearField],
        inv_ext: &NeonTwiddleExt,
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

        // head: stage n/2 (omega = 1), fused with stage n/4 when the total
        // stage count is even (so the remaining count is a multiple of 2)
        let mut dist = n / 2;
        let mut stages_left = log_n;
        if log_n % 2 == 0 {
            worker.scope(n / 4, |scope, geometry| {
                for thread_idx in 0..geometry.len() {
                    let start = geometry.get_chunk_start_pos(thread_idx);
                    let size = geometry.get_chunk_size(thread_idx);
                    let tw_addr = tw_raw.as_ptr() as usize;
                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
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
                for thread_idx in 0..geometry.len() {
                    let start = geometry.get_chunk_start_pos(thread_idx);
                    let size = geometry.get_chunk_size(thread_idx);
                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                        inv_head_single(base_addr as *mut BabyBearExt4, n, start..start + size);
                    });
                }
            });
            dist /= 2;
            stages_left -= 1;
        }

        // fused CT pairs: stage distance `dist` (groups n/(2*dist)) + `dist/2`
        while stages_left >= 2 {
            debug_assert!(dist >= 2);
            let half_d = dist / 2;
            // groups at the first stage of the pair x quads per group:
            // (n / (2*dist)) * (dist/2) = n/4
            let items = (n / (2 * dist)) * half_d;
            assert_eq!(items, n / 4);
            worker.scope(items, |scope, geometry| {
                for thread_idx in 0..geometry.len() {
                    let start = geometry.get_chunk_start_pos(thread_idx);
                    let size = geometry.get_chunk_size(thread_idx);
                    let tw_addr = tw_raw.as_ptr() as usize;
                    let (ao, bo) = (inv_ext.ao.as_ptr() as usize, inv_ext.bo.as_ptr() as usize);
                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
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
            for thread_idx in 0..geometry.len() {
                let start = geometry.get_chunk_start_pos(thread_idx);
                let size = geometry.get_chunk_size(thread_idx);
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                    let f = vdupq_n_u32(f_bits);
                    let base = base_addr as *mut BabyBearExt4;
                    for i in start..(start + size) {
                        st(base.add(i), mont_mul(ld(base.add(i)), f));
                    }
                });
            }
        });
        crate::utils::parallel_bitreverse_enumeration_inplace(&mut v, worker);
        v
    }

    /// NEON leaf FOLDING (evaluation form -> multilinear-coefficient form) for
    /// one whole coset of Ext4 values — the per-leaf `evals_to_multilinear_
    /// coeffs` butterfly network with every element as one NEON vector, the
    /// full leaf (<= 32 vectors) held in registers across all stages, and the
    /// per-pair `root * 2^-1` twiddles FUSED into one scalar Montgomery
    /// product per table entry (identical canonical values: `x*(r*t*R^-1))*
    /// R^-1 = ((x*r)*R^-1*t)*R^-1`).
    ///
    /// `offsets[k]` is the element offset of leaf slot `k` within the coset
    /// column, `hp_raw` the bit-reversed inverse-set-generator powers (raw
    /// values), `root_invs_raw[leaf]` the leaf's base root inverse (already
    /// including the coset offset inverse). `values_per_leaf` must be a power
    /// of two in `2..=32`.
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

        let mut buf_a = [vdupq_n_u32(0); 32];
        let mut buf_b = [vdupq_n_u32(0); 32];
        // fused per-stage twiddles: rt2[set] = mont(mont(root_inv, hp[set]), two_inv)
        let mut rt2 = [0u32; 16];

        for leaf_idx in leaf_range {
            // gather the leaf into registers
            for k in 0..n {
                buf_a[k] = ld(column.add(offsets[k] + leaf_idx));
            }
            let mut root_inv = root_invs_raw[leaf_idx];
            let two_inv_v = vdupq_n_u32(two_inv_raw);

            let mut src_is_a = true;
            for stage in 0..rounds {
                let num_existing = 1usize << stage;
                let block_len = n >> stage;
                let half = block_len / 2;
                for set_idx in 0..half {
                    let root = super::mont_mul_scalar(root_inv, hp_raw[set_idx]);
                    rt2[set_idx] = super::mont_mul_scalar(root, two_inv_raw);
                }
                let (src, dst): (&[uint32x4_t; 32], &mut [uint32x4_t; 32]) = if src_is_a {
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
                        dst[linear_base + set_idx] = mont_mul(sub(a, b), vdupq_n_u32(rt2[set_idx]));
                    }
                }
                src_is_a = !src_is_a;
                root_inv = super::mont_mul_scalar(root_inv, root_inv);
            }

            let fin: &[uint32x4_t; 32] = if src_is_a {
                &*(&buf_a as *const _)
            } else {
                &*(&buf_b as *const _)
            };
            for k in 0..n {
                st(column.add(offsets[k] + leaf_idx), fin[k]);
            }
        }
    }

    /// Serial coset conversion (flat per-coset task grids). Byte-identical to
    /// the scalar `ExtCoeffConvCtx::apply_serial`.
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
            for thread_idx in 0..geometry.len() {
                let start = geometry.get_chunk_start_pos(thread_idx);
                let size = geometry.get_chunk_size(thread_idx);
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
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

    /// Worker-parallel `monomial coefficients -> hypercube evals` (the ADD
    /// Mobius transform, strides 1 -> n/2, radix-4 fused vector adds) plus the
    /// final bit-reversal — the second O(1) batched-poly transformation, all
    /// threads on one array. Byte-identical to
    /// `multivariate_coeffs_into_hypercube_evals` + bitrev.
    pub fn hypercube_evals_from_monomial_form(
        mut v: Vec<BabyBearExt4>,
        worker: &Worker,
    ) -> Vec<BabyBearExt4> {
        let n = v.len();
        let log_n = n.trailing_zeros();
        const PAR_THRESHOLD: usize = 1 << 12;
        let base_addr = v.as_mut_ptr() as usize;

        #[inline(always)]
        unsafe fn add_radix4_items(
            a: *mut BabyBearExt4,
            s: usize, // smaller stride of the fused pair (s, 2s)
            item_range: core::ops::Range<usize>,
        ) {
            for t in item_range {
                let blk = t / s;
                let j = blk * (4 * s) + (t % s);
                let x0 = ld(a.add(j));
                let x1 = ld(a.add(j + s));
                let x2 = ld(a.add(j + 2 * s));
                let x3 = ld(a.add(j + 3 * s));
                // stride s: x1 += x0; x3 += x2. stride 2s: x2 += x0; x3 += x1'
                let n1 = add(x1, x0);
                let n3 = add(add(x3, x2), n1);
                let n2 = add(x2, x0);
                st(a.add(j + s), n1);
                st(a.add(j + 2 * s), n2);
                st(a.add(j + 3 * s), n3);
            }
        }
        #[inline(always)]
        unsafe fn add_single_items(
            a: *mut BabyBearExt4,
            s: usize,
            item_range: core::ops::Range<usize>,
        ) {
            for t in item_range {
                let blk = t / s;
                let j = blk * (2 * s) + (t % s);
                let x0 = ld(a.add(j));
                let x1 = ld(a.add(j + s));
                st(a.add(j + s), add(x1, x0));
            }
        }

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
            // natural (LSB) convention: the per-bit butterflies commute and
            // run in increasing-stride order, so the output is already the
            // natural-order hypercube evals (the old trailing bitreverse
            // adapted to the retired MSB sumcheck layout)
            return v;
        }

        let mut s = 1usize;
        let mut left = log_n;
        while left >= 2 {
            let cur_s = s;
            worker.scope(n / 4, |scope, geometry| {
                for thread_idx in 0..geometry.len() {
                    let start = geometry.get_chunk_start_pos(thread_idx);
                    let size = geometry.get_chunk_size(thread_idx);
                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
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
                for thread_idx in 0..geometry.len() {
                    let start = geometry.get_chunk_start_pos(thread_idx);
                    let size = geometry.get_chunk_size(thread_idx);
                    Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                        add_single_items(
                            base_addr as *mut BabyBearExt4,
                            cur_s,
                            start..start + size,
                        );
                    });
                }
            });
        }
        // natural (LSB) convention: see the serial branch note
        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::twiddles::precompute_all_twiddles_for_fft_serial;
    use field::{FieldExtension, Rand, TwoAdicField};
    use std::alloc::Global;

    /// Every Ext4 NEON kernel must equal its scalar reference exactly: serial
    /// + worker-parallel LDE vs `lde_coset_natural_seq_fused`, the parallel
    /// inverse (main domain -> monomial) vs `cache_friendly` + scale + bitrev,
    /// and the ADD transform + bitrev vs the prover-side reference sequence.
    #[test]
    fn ext4_neon_kernels_match_reference() {
        use field::baby_bear::ext4::BabyBearExt4;
        let worker = worker::Worker::new_with_num_threads(4);
        for log_n in [3u32, 4, 5, 8, 11, 12, 13, 14] {
            let n = 1usize << log_n;
            let mut rng = rand::rng();
            let input: Vec<BabyBearExt4> = (0..n)
                .map(|_| BabyBearExt4::random_element(&mut rng))
                .collect();
            let tw: Vec<BabyBearField, Global> =
                precompute_all_twiddles_for_fft_serial::<BabyBearField, Global, false>(n);
            let tw_inv: Vec<BabyBearField, Global> =
                precompute_all_twiddles_for_fft_serial::<BabyBearField, Global, true>(n);
            let ext = NeonTwiddleExt::build(&tw, n);
            let ext_inv = NeonTwiddleExt::build(&tw_inv, n);
            let offset =
                crate::field_utils::domain_generator_for_size::<BabyBearField>((n * 2) as u64);

            for off in [offset, BabyBearField::ONE] {
                let expected = crate::lde_coset_natural_seq_fused(&input, off, &tw);
                let got = ext4::lde_coset(&input, off, &tw, &ext);
                assert_eq!(got, expected, "ext4 serial LDE diverged at log_n={log_n}");
                let got = ext4::lde_coset_parallel(&input, off, &tw, &ext, &worker);
                assert_eq!(got, expected, "ext4 parallel LDE diverged at log_n={log_n}");
            }

            // inverse: main domain -> monomial form
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

            // monomial -> hypercube evals (+ bitrev): reference = per-variable
            // ADD sweeps then bitrev
            let mut expected = input.clone();
            {
                // reference ADD transform (mirror of the prover's
                // multivariate_coeffs_into_hypercube_evals)
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
                crate::utils::bitreverse_enumeration_inplace(&mut expected);
            }
            let got = ext4::hypercube_evals_from_monomial_form(input.clone(), &worker);
            assert_eq!(got, expected, "ext4 hc-evals diverged at log_n={log_n}");
        }
    }

    /// The NEON pipeline must equal `lde_coset_natural_seq_fused` exactly,
    /// across ppg-parity classes, both offset branches, and the tiny-size
    /// fallback path (log_n 1..3 degrade to the scalar reference).
    #[test]
    fn neon_lde_matches_reference() {
        for log_n in [1u32, 2, 3, 4, 5, 8, 11, 14, 16] {
            let n = 1usize << log_n;
            let mut rng = rand::rng();
            let input: Vec<BabyBearField> = (0..n)
                .map(|_| BabyBearField::random_element(&mut rng))
                .collect();
            let tw: Vec<BabyBearField, Global> =
                precompute_all_twiddles_for_fft_serial::<BabyBearField, Global, false>(n);
            let offset =
                crate::field_utils::domain_generator_for_size::<BabyBearField>((n * 2) as u64);
            let ext = NeonTwiddleExt::build(&tw, n);

            for off in [offset, BabyBearField::ONE] {
                let expected = crate::lde_coset_natural_seq_fused(&input, off, &tw);
                let got = lde_coset_neon(&input, off, &tw, &ext);
                assert_eq!(got, expected, "NEON pipeline diverged at log_n={log_n}");
            }
        }
    }
}
