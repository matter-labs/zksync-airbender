//! aarch64 NEON kernels for the windowed-sumcheck hot loops, specialized for
//! `BabyBearField` / `BabyBearExt4` (Montgomery form, `Ext4` = 4 contiguous
//! Montgomery `u32` limbs, 16-byte aligned).
//!
//! One `BabyBearExt4` maps onto one `uint32x4_t`; all lane arithmetic follows
//! the scalar implementations exactly:
//! * Montgomery multiply: 32x32->64 widening mults + REDC with
//!   `MONT_K = 0x77ffffff`, then one conditional subtract;
//! * `Ext4` multiplication uses the flat quartic table of
//!   `BabyBearExt4::mul_assign_flat_impl` (`alpha^2 = 11`, `beta^2 = alpha`):
//!   `a (x) b = sum_j a_j * col_j(b)` with
//!   `col_0(b) = [b0, b1, b2, b3]`, `col_1(b) = [11b1, b0, 11b3, b2]`,
//!   `col_2(b) = [11b3, b2, b0, b1]`, `col_3(b) = [11b2, 11b3, 11b1, b0]`.
//!
//! Callers dispatch here through `is_bb_pair::<F, E>()` and pointer casts; the
//! generic scalar code remains the fallback for every other field pair.

use core::arch::aarch64::*;

use ::field::baby_bear::base::BabyBearField;
use ::field::baby_bear::ext4::BabyBearExt4;
use ::field::{Field, PrimeField};

const P: u32 = 0x78000001;
const K: u32 = 0x77ffffff; // -P^{-1} mod 2^32 (matches BabyBearField::MONT_K)

const fn const_str_eq(a: &str, b: &str) -> bool {
    let (a, b) = (a.as_bytes(), b.as_bytes());
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0;
    while i < a.len() {
        if a[i] != b[i] {
            return false;
        }
        i += 1;
    }
    true
}

// Type identity is decided by comparing `core::any::type_name` in const context
// (a const-comparable `TypeId` is not available yet). The full type path is
// unambiguous within this workspace; even in a hypothetical duplicate-crate
// scenario the match would be a type with the same asserted layout and
// Montgomery semantics, so the pointer casts at the dispatch sites stay sound.
// Being `const fn` lets callers dispatch with `if const { ... }`, guaranteeing
// the untaken branch is compiled out.
#[inline(always)]
pub const fn is_bb_pair<F: 'static, E: 'static>() -> bool {
    const_str_eq(
        core::any::type_name::<F>(),
        core::any::type_name::<BabyBearField>(),
    ) && const_str_eq(
        core::any::type_name::<E>(),
        core::any::type_name::<BabyBearExt4>(),
    )
}

#[inline(always)]
pub const fn is_bb4<E: 'static>() -> bool {
    const_str_eq(
        core::any::type_name::<E>(),
        core::any::type_name::<BabyBearExt4>(),
    )
}

#[inline(always)]
pub(crate) unsafe fn mont_mul4(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    let p = vdupq_n_u32(P);
    let k = vdupq_n_u32(K);
    let prod_lo = vmull_u32(vget_low_u32(a), vget_low_u32(b));
    let prod_hi = vmull_high_u32(a, b);
    let lo32 = vcombine_u32(vmovn_u64(prod_lo), vmovn_u64(prod_hi));
    let m = vmulq_u32(lo32, k);
    let prod_lo = vmlal_u32(prod_lo, vget_low_u32(m), vget_low_u32(p));
    let prod_hi = vmlal_high_u32(prod_hi, m, p);
    let res = vcombine_u32(vshrn_n_u64::<32>(prod_lo), vshrn_n_u64::<32>(prod_hi));
    // res < 2P: conditional subtract via min (wrap-around makes the wrong branch huge)
    vminq_u32(res, vsubq_u32(res, p))
}

#[inline(always)]
pub(crate) unsafe fn add4(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    let sum = vaddq_u32(a, b);
    vminq_u32(sum, vsubq_u32(sum, vdupq_n_u32(P)))
}

#[inline(always)]
pub(crate) unsafe fn sub4(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    let diff = vsubq_u32(a, b);
    vminq_u32(diff, vaddq_u32(diff, vdupq_n_u32(P)))
}

#[inline(always)]
unsafe fn load_e(src: *const BabyBearExt4) -> uint32x4_t {
    vld1q_u32(src as *const u32)
}

#[inline(always)]
unsafe fn store_e(dst: *mut BabyBearExt4, v: uint32x4_t) {
    vst1q_u32(dst as *mut u32, v)
}

/// Montgomery form of 11 (the quadratic non-residue of the tower)
#[inline(always)]
pub(crate) fn r11() -> u32 {
    BabyBearField::new(11).raw_u32_value()
}

/// `a (x) b` for two variable `Ext4` values: build the permuted/scaled columns
/// of `b` (1 mult + 3 shuffles), then accumulate the lane-broadcast products.
#[inline(always)]
pub(crate) unsafe fn ext_mul_var(a: uint32x4_t, b: uint32x4_t, r11v: uint32x4_t) -> uint32x4_t {
    let e = mont_mul4(b, r11v); // [11b0, 11b1, 11b2, 11b3]
    let col1 = vtrn2q_u32(e, vrev64q_u32(b)); // [11b1, b0, 11b3, b2]
    let col2 = vextq_u32::<2>(col1, b); // [11b3, b2, b0, b1]
    let col3 = vextq_u32::<2>(e, col1); // [11b2, 11b3, 11b1, b0]

    let mut acc = mont_mul4(vdupq_laneq_u32::<0>(a), b);
    acc = add4(acc, mont_mul4(vdupq_laneq_u32::<1>(a), col1));
    acc = add4(acc, mont_mul4(vdupq_laneq_u32::<2>(a), col2));
    add4(acc, mont_mul4(vdupq_laneq_u32::<3>(a), col3))
}

/// Precomputed column form of a fixed `Ext4` multiplier: `mat_mul(m(b), a) = a (x) b`.
#[derive(Clone, Copy)]
pub struct ExtMatrix {
    cols: [uint32x4_t; 4],
}

impl ExtMatrix {
    #[inline(always)]
    pub fn new(b: &BabyBearExt4) -> Self {
        unsafe {
            let bv = load_e(b);
            let r11v = vdupq_n_u32(r11());
            let e = mont_mul4(bv, r11v);
            let col1 = vtrn2q_u32(e, vrev64q_u32(bv));
            let col2 = vextq_u32::<2>(col1, bv);
            let col3 = vextq_u32::<2>(e, col1);
            ExtMatrix {
                cols: [bv, col1, col2, col3],
            }
        }
    }
}

#[inline(always)]
pub(crate) unsafe fn mat_mul(m: &ExtMatrix, a: uint32x4_t) -> uint32x4_t {
    let mut acc = mont_mul4(vdupq_laneq_u32::<0>(a), m.cols[0]);
    acc = add4(acc, mont_mul4(vdupq_laneq_u32::<1>(a), m.cols[1]));
    acc = add4(acc, mont_mul4(vdupq_laneq_u32::<2>(a), m.cols[2]));
    add4(acc, mont_mul4(vdupq_laneq_u32::<3>(a), m.cols[3]))
}

// ---------------------------------------------------------------------------
// fold kernels (the transition / ext-only read paths)
// ---------------------------------------------------------------------------

/// `sum_i prefix[i] * base[row + i*stride]` — the 8-tap eq-weighted fold of a
/// base poly (ext-by-base per tap). Two independent accumulator chains break
/// the add-latency dependency across taps.
#[inline(always)]
pub unsafe fn fold8_base(
    src: *const BabyBearField,
    prefix: &[BabyBearExt4; 8],
    stride: usize,
    row: usize,
) -> BabyBearExt4 {
    let pv = prefix.as_ptr();
    let s = |i: usize| vdupq_n_u32((*src.add(row + i * stride)).raw_u32_value());
    let mut acc0 = mont_mul4(load_e(pv), s(0));
    let mut acc1 = mont_mul4(load_e(pv.add(1)), s(1));
    acc0 = add4(acc0, mont_mul4(load_e(pv.add(2)), s(2)));
    acc1 = add4(acc1, mont_mul4(load_e(pv.add(3)), s(3)));
    acc0 = add4(acc0, mont_mul4(load_e(pv.add(4)), s(4)));
    acc1 = add4(acc1, mont_mul4(load_e(pv.add(5)), s(5)));
    acc0 = add4(acc0, mont_mul4(load_e(pv.add(6)), s(6)));
    acc1 = add4(acc1, mont_mul4(load_e(pv.add(7)), s(7)));
    core::mem::transmute(add4(acc0, acc1))
}

/// Fused pair of 8-tap base folds at `row0`/`row1` sharing the prefix loads —
/// four independent accumulator chains keep the NEON pipes busy.
#[inline(always)]
pub unsafe fn fold8_base_x2(
    src: *const BabyBearField,
    prefix: &[BabyBearExt4; 8],
    stride: usize,
    row0: usize,
    row1: usize,
) -> (BabyBearExt4, BabyBearExt4) {
    let pv = prefix.as_ptr();
    let sa = |i: usize| vdupq_n_u32((*src.add(row0 + i * stride)).raw_u32_value());
    let sb = |i: usize| vdupq_n_u32((*src.add(row1 + i * stride)).raw_u32_value());
    let p0 = load_e(pv);
    let p1 = load_e(pv.add(1));
    let mut a0 = mont_mul4(p0, sa(0));
    let mut b0 = mont_mul4(p0, sb(0));
    let mut a1 = mont_mul4(p1, sa(1));
    let mut b1 = mont_mul4(p1, sb(1));
    let mut i = 2;
    while i < 8 {
        let pe = load_e(pv.add(i));
        let po = load_e(pv.add(i + 1));
        a0 = add4(a0, mont_mul4(pe, sa(i)));
        b0 = add4(b0, mont_mul4(pe, sb(i)));
        a1 = add4(a1, mont_mul4(po, sa(i + 1)));
        b1 = add4(b1, mont_mul4(po, sb(i + 1)));
        i += 2;
    }
    (
        core::mem::transmute(add4(a0, a1)),
        core::mem::transmute(add4(b0, b1)),
    )
}

/// `sum_i prefix[i] (x) ext[row + i*stride]` — the 8-tap fold of an ext poly.
#[inline(always)]
pub unsafe fn fold8_ext(
    src: *const BabyBearExt4,
    prefix: &[BabyBearExt4; 8],
    stride: usize,
    row: usize,
) -> BabyBearExt4 {
    let r11v = vdupq_n_u32(r11());
    let pv = prefix.as_ptr();
    let v = |i: usize| load_e(src.add(row + i * stride));
    let mut acc0 = ext_mul_var(load_e(pv), v(0), r11v);
    let mut acc1 = ext_mul_var(load_e(pv.add(1)), v(1), r11v);
    acc0 = add4(acc0, ext_mul_var(load_e(pv.add(2)), v(2), r11v));
    acc1 = add4(acc1, ext_mul_var(load_e(pv.add(3)), v(3), r11v));
    acc0 = add4(acc0, ext_mul_var(load_e(pv.add(4)), v(4), r11v));
    acc1 = add4(acc1, ext_mul_var(load_e(pv.add(5)), v(5), r11v));
    acc0 = add4(acc0, ext_mul_var(load_e(pv.add(6)), v(6), r11v));
    acc1 = add4(acc1, ext_mul_var(load_e(pv.add(7)), v(7), r11v));
    core::mem::transmute(add4(acc0, acc1))
}

/// Fused pair of 8-tap ext folds at `row0`/`row1`: each tap's prefix element is
/// matrix-ized once and applied to both rows' values, halving the shuffle and
/// non-residue-scaling work relative to two independent folds.
#[inline(always)]
pub unsafe fn fold8_ext_x2(
    src: *const BabyBearExt4,
    prefix: &[BabyBearExt4; 8],
    stride: usize,
    row0: usize,
    row1: usize,
) -> (BabyBearExt4, BabyBearExt4) {
    let va = |i: usize| load_e(src.add(row0 + i * stride));
    let vb = |i: usize| load_e(src.add(row1 + i * stride));
    let m0 = ExtMatrix::new(&prefix[0]);
    let m1 = ExtMatrix::new(&prefix[1]);
    let mut a0 = mat_mul(&m0, va(0));
    let mut b0 = mat_mul(&m0, vb(0));
    let mut a1 = mat_mul(&m1, va(1));
    let mut b1 = mat_mul(&m1, vb(1));
    let mut i = 2;
    while i < 8 {
        let me = ExtMatrix::new(&prefix[i]);
        let mo = ExtMatrix::new(&prefix[i + 1]);
        a0 = add4(a0, mat_mul(&me, va(i)));
        b0 = add4(b0, mat_mul(&me, vb(i)));
        a1 = add4(a1, mat_mul(&mo, va(i + 1)));
        b1 = add4(b1, mat_mul(&mo, vb(i + 1)));
        i += 2;
    }
    (
        core::mem::transmute(add4(a0, a1)),
        core::mem::transmute(add4(b0, b1)),
    )
}

/// `f0 + c*(f1 - f0)` for ext values at `(row, row + stride)`.
#[inline(always)]
pub unsafe fn fold2_ext(
    src: *const BabyBearExt4,
    challenge: &BabyBearExt4,
    stride: usize,
    row: usize,
) -> BabyBearExt4 {
    let r11v = vdupq_n_u32(r11());
    let f0 = load_e(src.add(row));
    let f1 = load_e(src.add(row + stride));
    let d = sub4(f1, f0);
    let t = ext_mul_var(load_e(challenge), d, r11v);
    core::mem::transmute(add4(f0, t))
}

/// `sum_i prefix[i] (x) ext[row + i*stride]` for 4 taps (window-2 fold).
#[inline(always)]
pub unsafe fn fold4_ext(
    src: *const BabyBearExt4,
    prefix: &[BabyBearExt4; 4],
    stride: usize,
    row: usize,
) -> BabyBearExt4 {
    let r11v = vdupq_n_u32(r11());
    let pv = prefix.as_ptr();
    let mut offset = row;
    let mut acc = ext_mul_var(load_e(pv), load_e(src.add(offset)), r11v);
    offset += stride;
    for i in 1..4 {
        let t = ext_mul_var(load_e(pv.add(i)), load_e(src.add(offset)), r11v);
        acc = add4(acc, t);
        offset += stride;
    }
    core::mem::transmute(acc)
}

// ---------------------------------------------------------------------------
// N-cell evaluation kernels (initial window + ext-only rounds)
// ---------------------------------------------------------------------------

/// `dst[i] += coeff * (a[i] * b[i])` over N cells, base*base operands.
#[inline(always)]
pub unsafe fn quad_base_cells<const N: usize>(
    dst: *mut BabyBearExt4,
    a: *const BabyBearField,
    b: *const BabyBearField,
    coeff: &BabyBearExt4,
) {
    let cv = load_e(coeff);
    let a = a as *const u32;
    let b = b as *const u32;
    // vectorize the base products 4 cells at a time
    let mut t = [0u32; N];
    let mut i = 0;
    while i + 4 <= N {
        let prod = mont_mul4(vld1q_u32(a.add(i)), vld1q_u32(b.add(i)));
        vst1q_u32(t.as_mut_ptr().add(i), prod);
        i += 4;
    }
    while i < N {
        // scalar Montgomery for the tail cells
        let av = *a.add(i);
        let bv = *b.add(i);
        let mut product = (av as u64).wrapping_mul(bv as u64);
        let m = (product as u32).wrapping_mul(K);
        product = product.wrapping_add((m as u64).wrapping_mul(P as u64));
        let mut r = (product >> 32) as u32;
        if r >= P {
            r -= P;
        }
        t[i] = r;
        i += 1;
    }
    for i in 0..N {
        let d = dst.add(i);
        let acc = add4(load_e(d), mont_mul4(cv, vdupq_n_u32(t[i])));
        store_e(d, acc);
    }
}

/// `dst[i] += coeff (x) (a_ext[i] * b_base[i])` over N cells.
#[inline(always)]
pub unsafe fn quad_mixed_cells<const N: usize>(
    dst: *mut BabyBearExt4,
    a_ext: *const BabyBearExt4,
    b_base: *const BabyBearField,
    coeff: &BabyBearExt4,
) {
    let m = ExtMatrix::new(coeff);
    let b = b_base as *const u32;
    for i in 0..N {
        let t = mont_mul4(load_e(a_ext.add(i)), vdupq_n_u32(*b.add(i)));
        let d = dst.add(i);
        store_e(d, add4(load_e(d), mat_mul(&m, t)));
    }
}

/// `dst[i] += coeff (x) (a[i] (x) b[i])` over N cells, ext*ext operands.
#[inline(always)]
pub unsafe fn quad_ext_cells<const N: usize>(
    dst: *mut BabyBearExt4,
    a: *const BabyBearExt4,
    b: *const BabyBearExt4,
    coeff: &BabyBearExt4,
) {
    let m = ExtMatrix::new(coeff);
    let r11v = vdupq_n_u32(r11());
    for i in 0..N {
        let t = ext_mul_var(load_e(a.add(i)), load_e(b.add(i)), r11v);
        let d = dst.add(i);
        store_e(d, add4(load_e(d), mat_mul(&m, t)));
    }
}

// ---------------------------------------------------------------------------
// lazy-accumulation kernels for the initial window (base*base + linear-base
// terms accumulate 64-bit lane products without per-term Montgomery reduction)
//
// Bound analysis (P = BabyBear, R = 2^32): each accumulated lane product is
// `coeff_j * t` with both factors canonical (< P), so < P^2 ~ 2^61.82. REDC
// needs its input below R*P ~ 2^62.91 to give a < 2P output, hence the static
// cadence: after every 2 accumulated products one conditional subtraction of
// R*P (a multiple of P, so a no-op mod P) restores the invariant `X < R*P`
// (X < R*P + 2*P^2 < 2^64 never overflows, and X - R*P < 2*P^2 < R*P).
// A single REDC + canonicalization per row happens in `lazy_finalize_cells`.
// ---------------------------------------------------------------------------

const RP: u64 = (P as u64) << 32;

/// One conditional subtraction of `R*P` on every lane of the u64 accumulator.
#[inline(always)]
pub unsafe fn lazy_condsub_cells<const N: usize>(acc: *mut u64) {
    let rp = vdupq_n_u64(RP);
    for i in 0..(2 * N) {
        let p = acc.add(2 * i);
        let x = vld1q_u64(p);
        let mask = vcgeq_u64(x, rp);
        vst1q_u64(p, vsubq_u64(x, vandq_u64(mask, rp)));
    }
}

/// `acc[cell] += coeff * (a[cell] * b[cell])` with the base product reduced
/// once and the ext-by-base scaling deferred: raw 64-bit lane products are
/// added into the accumulator (2 vmlal per cell instead of a full Montgomery
/// multiply + add).
#[inline(always)]
pub unsafe fn lazy_quad_base_cells<const N: usize>(
    acc: *mut u64,
    a: *const BabyBearField,
    b: *const BabyBearField,
    coeff: &BabyBearExt4,
) {
    let cv = load_e(coeff);
    let cv_lo = vget_low_u32(cv);
    let a = a as *const u32;
    let b = b as *const u32;
    let mut t = [0u32; N];
    let mut i = 0;
    while i + 4 <= N {
        let prod = mont_mul4(vld1q_u32(a.add(i)), vld1q_u32(b.add(i)));
        vst1q_u32(t.as_mut_ptr().add(i), prod);
        i += 4;
    }
    while i < N {
        let av = *a.add(i);
        let bv = *b.add(i);
        let mut product = (av as u64).wrapping_mul(bv as u64);
        let m = (product as u32).wrapping_mul(K);
        product = product.wrapping_add((m as u64).wrapping_mul(P as u64));
        let mut r = (product >> 32) as u32;
        if r >= P {
            r -= P;
        }
        t[i] = r;
        i += 1;
    }
    for i in 0..N {
        let p = acc.add(4 * i);
        let lo = vmlal_u32(vld1q_u64(p), cv_lo, vdup_n_u32(t[i]));
        let hi = vmlal_high_u32(vld1q_u64(p.add(2)), cv, vdupq_n_u32(t[i]));
        vst1q_u64(p, lo);
        vst1q_u64(p.add(2), hi);
    }
}

/// `acc[cell] += coeff * a_base[cell]` over the 8 binary cells, lazily.
#[inline(always)]
pub unsafe fn lazy_linear_base_27(acc: *mut u64, a: *const BabyBearField, coeff: &BabyBearExt4) {
    let cv = load_e(coeff);
    let cv_lo = vget_low_u32(cv);
    let a = a as *const u32;
    for i in 0..2 {
        let offset = 9 * i;
        for j in 0..2 {
            let offset = offset + 3 * j;
            for kk in 0..2 {
                let idx = offset + kk;
                let p = acc.add(4 * idx);
                let t = *a.add(idx);
                let lo = vmlal_u32(vld1q_u64(p), cv_lo, vdup_n_u32(t));
                let hi = vmlal_high_u32(vld1q_u64(p.add(2)), cv, vdupq_n_u32(t));
                vst1q_u64(p, lo);
                vst1q_u64(p.add(2), hi);
            }
        }
    }
}

/// Final reduction of the lazy accumulator: one conditional `R*P` subtraction,
/// one REDC and one canonicalization per lane; writes canonical `Ext4` cells
/// and zeroes the accumulator for the next row.
#[inline(always)]
pub unsafe fn lazy_finalize_cells<const N: usize>(acc: *mut u64, out: *mut BabyBearExt4) {
    let rp = vdupq_n_u64(RP);
    let p2 = vdup_n_u32(P);
    let k2 = vdup_n_u32(K);
    let pq = vdupq_n_u32(P);
    for i in 0..N {
        let ptr = acc.add(4 * i);
        let mut lo = vld1q_u64(ptr);
        let mut hi = vld1q_u64(ptr.add(2));
        lo = vsubq_u64(lo, vandq_u64(vcgeq_u64(lo, rp), rp));
        hi = vsubq_u64(hi, vandq_u64(vcgeq_u64(hi, rp), rp));
        // REDC: X -> (X + (X*K mod R)*P) / R, X < R*P so the result is < 2P
        let m_lo = vmul_u32(vmovn_u64(lo), k2);
        let m_hi = vmul_u32(vmovn_u64(hi), k2);
        lo = vmlal_u32(lo, m_lo, p2);
        hi = vmlal_u32(hi, m_hi, p2);
        let r = vcombine_u32(vshrn_n_u64::<32>(lo), vshrn_n_u64::<32>(hi));
        let r = vminq_u32(r, vsubq_u32(r, pq));
        store_e(out.add(i), r);
        vst1q_u64(ptr, vdupq_n_u64(0));
        vst1q_u64(ptr.add(2), vdupq_n_u64(0));
    }
}

// ---------------------------------------------------------------------------
// inner-linear-form (bracket) materialization for bracket-preserving evaluation
// ---------------------------------------------------------------------------

/// `dst[cell] += src[cell]` over 27 base cells.
#[inline(always)]
pub unsafe fn form_add_27(dst: *mut BabyBearField, src: *const BabyBearField) {
    let d = dst as *mut u32;
    let s = src as *const u32;
    let mut i = 0;
    while i + 4 <= 24 {
        vst1q_u32(d.add(i), add4(vld1q_u32(d.add(i)), vld1q_u32(s.add(i))));
        i += 4;
    }
    for i in 24..27 {
        (*dst.add(i)).add_assign(&*src.add(i));
    }
}

/// `dst[cell] -= src[cell]` over 27 base cells.
#[inline(always)]
pub unsafe fn form_sub_27(dst: *mut BabyBearField, src: *const BabyBearField) {
    let d = dst as *mut u32;
    let s = src as *const u32;
    let mut i = 0;
    while i + 4 <= 24 {
        vst1q_u32(d.add(i), sub4(vld1q_u32(d.add(i)), vld1q_u32(s.add(i))));
        i += 4;
    }
    for i in 24..27 {
        (*dst.add(i)).sub_assign(&*src.add(i));
    }
}

/// `dst[cell] += c * src[cell]` over 27 base cells.
#[inline(always)]
pub unsafe fn form_muladd_27(dst: *mut BabyBearField, src: *const BabyBearField, c: BabyBearField) {
    let d = dst as *mut u32;
    let s = src as *const u32;
    let cv = vdupq_n_u32(c.raw_u32_value());
    let mut i = 0;
    while i + 4 <= 24 {
        vst1q_u32(
            d.add(i),
            add4(vld1q_u32(d.add(i)), mont_mul4(vld1q_u32(s.add(i)), cv)),
        );
        i += 4;
    }
    for i in 24..27 {
        let mut t = *src.add(i);
        t.mul_assign(&c);
        (*dst.add(i)).add_assign(&t);
    }
}

/// `dst[cell] += coeff * a_base[cell]` over the 8 binary cells of the 27-grid.
#[inline(always)]
pub unsafe fn linear_base_27(
    dst: *mut BabyBearExt4,
    a: *const BabyBearField,
    coeff: &BabyBearExt4,
) {
    let cv = load_e(coeff);
    let a = a as *const u32;
    for i in 0..2 {
        let offset = 9 * i;
        for j in 0..2 {
            let offset = offset + 3 * j;
            for kk in 0..2 {
                let idx = offset + kk;
                let d = dst.add(idx);
                store_e(d, add4(load_e(d), mont_mul4(cv, vdupq_n_u32(*a.add(idx)))));
            }
        }
    }
}

/// `dst[cell] += coeff (x) a_ext[cell]` over the 8 binary cells of the 27-grid.
#[inline(always)]
pub unsafe fn linear_ext_27(dst: *mut BabyBearExt4, a: *const BabyBearExt4, coeff: &BabyBearExt4) {
    let m = ExtMatrix::new(coeff);
    for i in 0..2 {
        let offset = 9 * i;
        for j in 0..2 {
            let offset = offset + 3 * j;
            for kk in 0..2 {
                let idx = offset + kk;
                let d = dst.add(idx);
                store_e(d, add4(load_e(d), mat_mul(&m, load_e(a.add(idx)))));
            }
        }
    }
}

/// `acc[i] += evals[i] (x) eq` over N cells (the per-row eq-suffix application).
#[inline(always)]
pub unsafe fn accumulate_times_eq<const N: usize>(
    acc: *mut BabyBearExt4,
    evals: *const BabyBearExt4,
    eq: &BabyBearExt4,
) {
    let m = ExtMatrix::new(eq);
    for i in 0..N {
        let d = acc.add(i);
        store_e(d, add4(load_e(d), mat_mul(&m, load_e(evals.add(i)))));
    }
}

// ---------------------------------------------------------------------------
// SoA row-blocked kernels: 4 consecutive rows per NEON vector
//
// Within a per-thread row range every tap of the 27-cell read is CONTIGUOUS
// across rows, so 4 rows load as one `vld1q`. Layouts (raw u32 buffers):
// * base grid per poly:  [27 cells][4 rows]
// * ext grid per poly:   [27 cells][4 limbs][4 rows] (transposed to SoA)
// * lazy accumulator:    [27 cells][4 limbs][4 rows] u64
// * reduced scratch / chunk accumulator: same shape, canonical u32
// Term evaluation vectorizes over the 4 rows instead of over ext limbs.
// ---------------------------------------------------------------------------

/// 4x4 u32 transpose: rows (AoS ext elements) -> limb-major vectors.
#[inline(always)]
unsafe fn transpose4x4(
    r0: uint32x4_t,
    r1: uint32x4_t,
    r2: uint32x4_t,
    r3: uint32x4_t,
) -> [uint32x4_t; 4] {
    let t0 = vtrn1q_u32(r0, r1);
    let t1 = vtrn2q_u32(r0, r1);
    let t2 = vtrn1q_u32(r2, r3);
    let t3 = vtrn2q_u32(r2, r3);
    [
        vreinterpretq_u32_u64(vtrn1q_u64(
            vreinterpretq_u64_u32(t0),
            vreinterpretq_u64_u32(t2),
        )),
        vreinterpretq_u32_u64(vtrn1q_u64(
            vreinterpretq_u64_u32(t1),
            vreinterpretq_u64_u32(t3),
        )),
        vreinterpretq_u32_u64(vtrn2q_u64(
            vreinterpretq_u64_u32(t0),
            vreinterpretq_u64_u32(t2),
        )),
        vreinterpretq_u32_u64(vtrn2q_u64(
            vreinterpretq_u64_u32(t1),
            vreinterpretq_u64_u32(t3),
        )),
    ]
}

/// Read the 8 binary cells of a base poly for rows `row..row+4` (one vld1q per
/// tap) and extrapolate the 19 infinity cells with vectorized subs.
#[inline(always)]
pub unsafe fn soa_read_base_grid(
    dst: *mut u32, // [27][4]
    src: *const BabyBearField,
    input_size: usize,
    row: usize,
    interpolate: bool,
) {
    let src = src as *const u32;
    let cell = |c: usize| dst.add(4 * c);
    let stride_step = input_size / 2;
    for x0 in 0..2 {
        let stride = stride_step * x0;
        let dst_offset = 9 * x0;
        for x1 in 0..2 {
            let stride_step = stride_step / 2;
            let stride = stride + x1 * stride_step;
            let dst_offset = dst_offset + 3 * x1;
            let stride_step = stride_step / 2;
            let v0 = vld1q_u32(src.add(stride + row));
            let v1 = vld1q_u32(src.add(stride + stride_step + row));
            vst1q_u32(cell(dst_offset), v0);
            vst1q_u32(cell(dst_offset + 1), v1);
            if interpolate {
                vst1q_u32(cell(dst_offset + 2), sub4(v1, v0));
            }
        }
        if interpolate {
            for x2 in 0..3 {
                let a = vld1q_u32(cell(dst_offset + x2));
                let b = vld1q_u32(cell(dst_offset + 3 + x2));
                vst1q_u32(cell(dst_offset + 6 + x2), sub4(b, a));
            }
        }
    }
    if interpolate {
        for x1 in 0..3 {
            let o = 3 * x1;
            for x2 in 0..3 {
                let a = vld1q_u32(cell(o + x2));
                let b = vld1q_u32(cell(9 + o + x2));
                vst1q_u32(cell(18 + o + x2), sub4(b, a));
            }
        }
    }
}

/// Read the 8 binary cells of an ext poly for rows `row..row+4`, transposing
/// each cell to limb-major SoA, and extrapolate the infinity cells per limb.
#[inline(always)]
pub unsafe fn soa_read_ext_grid(
    dst: *mut u32, // [27][4 limbs][4 rows]
    src: *const BabyBearExt4,
    input_size: usize,
    row: usize,
    interpolate: bool,
) {
    let src = src as *const u32;
    let cell = |c: usize, l: usize| dst.add(16 * c + 4 * l);
    let stride_step = input_size / 2;
    for x0 in 0..2 {
        let stride = stride_step * x0;
        let dst_offset = 9 * x0;
        for x1 in 0..2 {
            let stride_step = stride_step / 2;
            let stride = stride + x1 * stride_step;
            let dst_offset = dst_offset + 3 * x1;
            let stride_step = stride_step / 2;
            for (o, idx) in [(dst_offset, stride + row), (dst_offset + 1, stride + stride_step + row)] {
                let p = src.add(4 * idx);
                let t = transpose4x4(
                    vld1q_u32(p),
                    vld1q_u32(p.add(4)),
                    vld1q_u32(p.add(8)),
                    vld1q_u32(p.add(12)),
                );
                for l in 0..4 {
                    vst1q_u32(cell(o, l), t[l]);
                }
            }
            if interpolate {
                for l in 0..4 {
                    let a = vld1q_u32(cell(dst_offset, l));
                    let b = vld1q_u32(cell(dst_offset + 1, l));
                    vst1q_u32(cell(dst_offset + 2, l), sub4(b, a));
                }
            }
        }
        if interpolate {
            for x2 in 0..3 {
                for l in 0..4 {
                    let a = vld1q_u32(cell(dst_offset + x2, l));
                    let b = vld1q_u32(cell(dst_offset + 3 + x2, l));
                    vst1q_u32(cell(dst_offset + 6 + x2, l), sub4(b, a));
                }
            }
        }
    }
    if interpolate {
        for x1 in 0..3 {
            let o = 3 * x1;
            for x2 in 0..3 {
                for l in 0..4 {
                    let a = vld1q_u32(cell(o + x2, l));
                    let b = vld1q_u32(cell(9 + o + x2, l));
                    vst1q_u32(cell(18 + o + x2, l), sub4(b, a));
                }
            }
        }
    }
}

/// Row-pointwise `Ext4` multiplication in SoA form (flat quartic table).
#[inline(always)]
unsafe fn soa_ext_mul(
    a: &[uint32x4_t; 4],
    b: &[uint32x4_t; 4],
    r11v: uint32x4_t,
) -> [uint32x4_t; 4] {
    let p00 = mont_mul4(a[0], b[0]);
    let p01 = mont_mul4(a[0], b[1]);
    let p02 = mont_mul4(a[0], b[2]);
    let p03 = mont_mul4(a[0], b[3]);
    let p10 = mont_mul4(a[1], b[0]);
    let p11 = mont_mul4(a[1], b[1]);
    let p12 = mont_mul4(a[1], b[2]);
    let p13 = mont_mul4(a[1], b[3]);
    let p20 = mont_mul4(a[2], b[0]);
    let p21 = mont_mul4(a[2], b[1]);
    let p22 = mont_mul4(a[2], b[2]);
    let p23 = mont_mul4(a[2], b[3]);
    let p30 = mont_mul4(a[3], b[0]);
    let p31 = mont_mul4(a[3], b[1]);
    let p32 = mont_mul4(a[3], b[2]);
    let p33 = mont_mul4(a[3], b[3]);
    // out0 = p00 + 11*(p11 + p23 + p32)
    let out0 = add4(p00, mont_mul4(add4(add4(p11, p23), p32), r11v));
    // out1 = p01 + p10 + p22 + 11*p33
    let out1 = add4(add4(p01, p10), add4(p22, mont_mul4(p33, r11v)));
    // out2 = p02 + p20 + 11*(p13 + p31)
    let out2 = add4(add4(p02, p20), mont_mul4(add4(p13, p31), r11v));
    // out3 = p03 + p12 + p21 + p30
    let out3 = add4(add4(p03, p12), add4(p21, p30));
    [out0, out1, out2, out3]
}

/// `acc[cell] += coeff * (a[cell] * b[cell])` over 27 cells x 4 rows, lazily
/// (raw 64-bit products, same cadence/bounds as the AoS lazy kernels).
#[inline(always)]
pub unsafe fn soa_quad_bb_lazy<const N: usize>(
    acc: *mut u64, // [N][4 limbs][4 rows]
    a: *const u32,
    b: *const u32,
    coeff: &BabyBearExt4,
) {
    let climbs: [u32; 4] = core::mem::transmute(*coeff);
    for c in 0..N {
        let t = mont_mul4(vld1q_u32(a.add(4 * c)), vld1q_u32(b.add(4 * c)));
        let t_lo = vget_low_u32(t);
        for l in 0..4 {
            let p = acc.add(16 * c + 4 * l);
            let cl = climbs[l];
            let lo = vmlal_u32(vld1q_u64(p), t_lo, vdup_n_u32(cl));
            let hi = vmlal_high_u32(vld1q_u64(p.add(2)), t, vdupq_n_u32(cl));
            vst1q_u64(p, lo);
            vst1q_u64(p.add(2), hi);
        }
    }
}

/// `acc[cell] += coeff * a[cell]` over the 8 binary cells, lazily.
#[inline(always)]
pub unsafe fn soa_lin_base_lazy(acc: *mut u64, a: *const u32, coeff: &BabyBearExt4) {
    let climbs: [u32; 4] = core::mem::transmute(*coeff);
    for i in 0..2 {
        let offset = 9 * i;
        for j in 0..2 {
            let offset = offset + 3 * j;
            for kk in 0..2 {
                let c = offset + kk;
                let t = vld1q_u32(a.add(4 * c));
                let t_lo = vget_low_u32(t);
                for l in 0..4 {
                    let p = acc.add(16 * c + 4 * l);
                    let cl = climbs[l];
                    let lo = vmlal_u32(vld1q_u64(p), t_lo, vdup_n_u32(cl));
                    let hi = vmlal_high_u32(vld1q_u64(p.add(2)), t, vdupq_n_u32(cl));
                    vst1q_u64(p, lo);
                    vst1q_u64(p.add(2), hi);
                }
            }
        }
    }
}

/// Conditional `R*P` subtraction over the whole SoA lazy accumulator.
#[inline(always)]
pub unsafe fn soa_lazy_condsub<const N: usize>(acc: *mut u64) {
    let rp = vdupq_n_u64(RP);
    for i in 0..(N * 8) {
        let p = acc.add(2 * i);
        let x = vld1q_u64(p);
        let mask = vcgeq_u64(x, rp);
        vst1q_u64(p, vsubq_u64(x, vandq_u64(mask, rp)));
    }
}

/// Final REDC + canonicalization of the SoA lazy accumulator into canonical
/// SoA u32 cells; zeroes the accumulator.
#[inline(always)]
pub unsafe fn soa_lazy_finalize<const N: usize>(acc: *mut u64, out: *mut u32) {
    let rp = vdupq_n_u64(RP);
    let p2 = vdup_n_u32(P);
    let k2 = vdup_n_u32(K);
    let pq = vdupq_n_u32(P);
    for i in 0..(N * 4) {
        let ptr = acc.add(4 * i);
        let mut lo = vld1q_u64(ptr);
        let mut hi = vld1q_u64(ptr.add(2));
        lo = vsubq_u64(lo, vandq_u64(vcgeq_u64(lo, rp), rp));
        hi = vsubq_u64(hi, vandq_u64(vcgeq_u64(hi, rp), rp));
        let m_lo = vmul_u32(vmovn_u64(lo), k2);
        let m_hi = vmul_u32(vmovn_u64(hi), k2);
        lo = vmlal_u32(lo, m_lo, p2);
        hi = vmlal_u32(hi, m_hi, p2);
        let r = vcombine_u32(vshrn_n_u64::<32>(lo), vshrn_n_u64::<32>(hi));
        vst1q_u32(out.add(4 * i), vminq_u32(r, vsubq_u32(r, pq)));
        vst1q_u64(ptr, vdupq_n_u64(0));
        vst1q_u64(ptr.add(2), vdupq_n_u64(0));
    }
}

/// `dst[cell] += coeff (x) (a_ext[cell] (x) b_ext[cell])` over 27 cells x 4 rows
/// into the reduced SoA scratch.
#[inline(always)]
pub unsafe fn soa_quad_ee(
    dst: *mut u32,
    a: *const u32,
    b: *const u32,
    coeff_bcast: &[uint32x4_t; 4],
    r11v: uint32x4_t,
) {
    for c in 0..27 {
        let av: [uint32x4_t; 4] = core::array::from_fn(|l| vld1q_u32(a.add(16 * c + 4 * l)));
        let bv: [uint32x4_t; 4] = core::array::from_fn(|l| vld1q_u32(b.add(16 * c + 4 * l)));
        let v = soa_ext_mul(&av, &bv, r11v);
        let w = soa_ext_mul(&v, coeff_bcast, r11v);
        for l in 0..4 {
            let p = dst.add(16 * c + 4 * l);
            vst1q_u32(p, add4(vld1q_u32(p), w[l]));
        }
    }
}

/// `dst[cell] += coeff (x) (a_ext[cell] * b_base[cell])` over 27 cells x 4 rows.
#[inline(always)]
pub unsafe fn soa_quad_be<const N: usize>(
    dst: *mut u32,
    a_ext: *const u32,
    b_base: *const u32,
    coeff_bcast: &[uint32x4_t; 4],
    r11v: uint32x4_t,
) {
    for c in 0..N {
        let bv = vld1q_u32(b_base.add(4 * c));
        let t: [uint32x4_t; 4] =
            core::array::from_fn(|l| mont_mul4(vld1q_u32(a_ext.add(16 * c + 4 * l)), bv));
        let w = soa_ext_mul(&t, coeff_bcast, r11v);
        for l in 0..4 {
            let p = dst.add(16 * c + 4 * l);
            vst1q_u32(p, add4(vld1q_u32(p), w[l]));
        }
    }
}

/// `dst[cell] += coeff (x) a_ext[cell]` over the 8 binary cells x 4 rows.
#[inline(always)]
pub unsafe fn soa_lin_ext(
    dst: *mut u32,
    a_ext: *const u32,
    coeff_bcast: &[uint32x4_t; 4],
    r11v: uint32x4_t,
) {
    for i in 0..2 {
        let offset = 9 * i;
        for j in 0..2 {
            let offset = offset + 3 * j;
            for kk in 0..2 {
                let c = offset + kk;
                let av: [uint32x4_t; 4] =
                    core::array::from_fn(|l| vld1q_u32(a_ext.add(16 * c + 4 * l)));
                let w = soa_ext_mul(&av, coeff_bcast, r11v);
                for l in 0..4 {
                    let p = dst.add(16 * c + 4 * l);
                    vst1q_u32(p, add4(vld1q_u32(p), w[l]));
                }
            }
        }
    }
}

/// `dst[cell] += constant` over the 8 binary cells x 4 rows.
#[inline(always)]
pub unsafe fn soa_add_const(dst: *mut u32, const_bcast: &[uint32x4_t; 4]) {
    for i in 0..2 {
        let offset = 9 * i;
        for j in 0..2 {
            let offset = offset + 3 * j;
            for kk in 0..2 {
                let c = offset + kk;
                for l in 0..4 {
                    let p = dst.add(16 * c + 4 * l);
                    vst1q_u32(p, add4(vld1q_u32(p), const_bcast[l]));
                }
            }
        }
    }
}

/// Per-block eq application: `acc[cell] += (lazy_out[cell] + reduced[cell]) (x) eq`
/// where `eq` is the 4-row eq block in SoA form; also zeroes `reduced`.
#[inline(always)]
pub unsafe fn soa_apply_eq_and_accumulate<const N: usize>(
    acc: *mut u32,
    lazy_out: *const u32,
    reduced: *mut u32,
    eq_soa: &[uint32x4_t; 4],
    r11v: uint32x4_t,
) {
    for c in 0..N {
        let v: [uint32x4_t; 4] = core::array::from_fn(|l| {
            add4(
                vld1q_u32(lazy_out.add(16 * c + 4 * l)),
                vld1q_u32(reduced.add(16 * c + 4 * l)),
            )
        });
        let w = soa_ext_mul(&v, eq_soa, r11v);
        for l in 0..4 {
            let p = acc.add(16 * c + 4 * l);
            vst1q_u32(p, add4(vld1q_u32(p), w[l]));
            vst1q_u32(reduced.add(16 * c + 4 * l), vdupq_n_u32(0));
        }
    }
}

/// Transpose a block of 4 consecutive AoS ext values into limb-major SoA.
#[inline(always)]
pub unsafe fn soa_transpose_ext4(src: *const BabyBearExt4) -> [uint32x4_t; 4] {
    let p = src as *const u32;
    transpose4x4(
        vld1q_u32(p),
        vld1q_u32(p.add(4)),
        vld1q_u32(p.add(8)),
        vld1q_u32(p.add(12)),
    )
}

/// Broadcast the limbs of one ext value to row vectors.
#[inline(always)]
pub unsafe fn soa_broadcast_ext(v: &BabyBearExt4) -> [uint32x4_t; 4] {
    let limbs: [u32; 4] = core::mem::transmute(*v);
    core::array::from_fn(|l| vdupq_n_u32(limbs[l]))
}

/// Montgomery form of the non-residue as a row vector, for the SoA kernels.
#[inline(always)]
pub fn soa_r11v() -> uint32x4_t {
    unsafe { vdupq_n_u32(r11()) }
}

// ---------------------------------------------------------------------------
// SoA fold kernels (transition + ext-only passes), 4 rows per vector
// ---------------------------------------------------------------------------

/// Per-tap multiplication table of a fixed ext multiplier `p`, broadcast to row
/// vectors: `(p (x) v)_j = sum_k m[j][k] * v_k` with every entry canonical
/// (the `11*p_i` entries are REDC'd once at build time), so tap products stay
/// below `P^2` and are lazy-accumulable.
#[derive(Clone, Copy)]
pub struct SoaExtTable {
    m: [[uint32x4_t; 4]; 4],
}

impl SoaExtTable {
    #[inline(always)]
    pub fn new(p: &BabyBearExt4) -> Self {
        let l: [u32; 4] = unsafe { core::mem::transmute(*p) };
        let e11 = BabyBearField::new(11);
        let scaled: [u32; 4] = core::array::from_fn(|i| {
            let mut t = BabyBearField::from_raw_u32(l[i]);
            t.mul_assign(&e11);
            t.raw_u32_value()
        });
        // flat table with `a = p` fixed:
        // out0 = p0 v0 + 11p1 v1 + 11p3 v2 + 11p2 v3
        // out1 = p1 v0 + p0 v1 + p2 v2 + 11p3 v3
        // out2 = p2 v0 + 11p3 v1 + p0 v2 + 11p1 v3
        // out3 = p3 v0 + p2 v1 + p1 v2 + p0 v3
        let rows: [[u32; 4]; 4] = [
            [l[0], scaled[1], scaled[3], scaled[2]],
            [l[1], l[0], l[2], scaled[3]],
            [l[2], scaled[3], l[0], scaled[1]],
            [l[3], l[2], l[1], l[0]],
        ];
        SoaExtTable {
            m: unsafe {
                core::array::from_fn(|j| core::array::from_fn(|k| vdupq_n_u32(rows[j][k])))
            },
        }
    }

    /// Direct (reduced) application: `p (x) v` for a SoA row-vector value.
    #[inline(always)]
    pub unsafe fn apply(&self, v: &[uint32x4_t; 4]) -> [uint32x4_t; 4] {
        core::array::from_fn(|j| {
            let mut acc = mont_mul4(self.m[j][0], v[0]);
            acc = add4(acc, mont_mul4(self.m[j][1], v[1]));
            acc = add4(acc, mont_mul4(self.m[j][2], v[2]));
            add4(acc, mont_mul4(self.m[j][3], v[3]))
        })
    }
}

/// Lazy u64x2-pair accumulator for one SoA limb (4 rows), with the standard
/// `R*P` conditional-subtract invariant.
#[derive(Clone, Copy)]
struct LazyLimb {
    lo: uint64x2_t,
    hi: uint64x2_t,
}

impl LazyLimb {
    #[inline(always)]
    unsafe fn zero() -> Self {
        LazyLimb {
            lo: vdupq_n_u64(0),
            hi: vdupq_n_u64(0),
        }
    }

    #[inline(always)]
    unsafe fn mla(&mut self, coeff: uint32x4_t, v: uint32x4_t) {
        self.lo = vmlal_u32(self.lo, vget_low_u32(coeff), vget_low_u32(v));
        self.hi = vmlal_high_u32(self.hi, coeff, v);
    }

    #[inline(always)]
    unsafe fn condsub(&mut self) {
        let rp = vdupq_n_u64(RP);
        self.lo = vsubq_u64(self.lo, vandq_u64(vcgeq_u64(self.lo, rp), rp));
        self.hi = vsubq_u64(self.hi, vandq_u64(vcgeq_u64(self.hi, rp), rp));
    }

    #[inline(always)]
    unsafe fn redc(mut self) -> uint32x4_t {
        self.condsub();
        let p2 = vdup_n_u32(P);
        let k2 = vdup_n_u32(K);
        let m_lo = vmul_u32(vmovn_u64(self.lo), k2);
        let m_hi = vmul_u32(vmovn_u64(self.hi), k2);
        let lo = vmlal_u32(self.lo, m_lo, p2);
        let hi = vmlal_u32(self.hi, m_hi, p2);
        let r = vcombine_u32(vshrn_n_u64::<32>(lo), vshrn_n_u64::<32>(hi));
        vminq_u32(r, vsubq_u32(r, vdupq_n_u32(P)))
    }
}

/// 8-tap fold of a base poly for 4 consecutive rows, SoA output (limb-major):
/// `out_j = sum_i prefix[i]_j * base[pos + i*stride .. +4]`, accumulated lazily
/// per limb (one vld1q per tap, 2 vmlal per tap per limb).
#[inline(always)]
pub unsafe fn soa_fold8_base(
    src: *const BabyBearField,
    prefix_limbs: &[[uint32x4_t; 4]; 8], // [tap][limb] broadcast
    stride: usize,
    pos: usize,
) -> [uint32x4_t; 4] {
    let src = src as *const u32;
    let mut acc = [LazyLimb::zero(); 4];
    for i in 0..8 {
        let taps = vld1q_u32(src.add(pos + i * stride));
        for j in 0..4 {
            acc[j].mla(prefix_limbs[i][j], taps);
        }
        if i % 2 == 1 {
            for j in 0..4 {
                acc[j].condsub();
            }
        }
    }
    core::array::from_fn(|j| acc[j].redc())
}

/// 8-tap fold of an ext poly for 4 consecutive rows, SoA output: per tap the
/// AoS block is transposed to limb-major and the tap's precomputed table rows
/// are lazy-accumulated (4 products per output limb per tap).
#[inline(always)]
pub unsafe fn soa_fold8_ext(
    src: *const BabyBearExt4,
    tables: &[SoaExtTable; 8],
    stride: usize,
    pos: usize,
) -> [uint32x4_t; 4] {
    let mut acc = [LazyLimb::zero(); 4];
    for i in 0..8 {
        let v = soa_transpose_ext4(src.add(pos + i * stride));
        let t = &tables[i];
        for j in 0..4 {
            acc[j].mla(t.m[j][0], v[0]);
            acc[j].mla(t.m[j][1], v[1]);
            acc[j].condsub();
            acc[j].mla(t.m[j][2], v[2]);
            acc[j].mla(t.m[j][3], v[3]);
            acc[j].condsub();
        }
    }
    core::array::from_fn(|j| acc[j].redc())
}

/// LSB-layout 8-tap fold of a base poly, 4 consecutive OUTPUT rows per call:
/// the rows' 32 contiguous taps are transposed in-register (2 x 4x4) into
/// tap-column vectors (lanes = rows), then lazy-accumulated against the
/// broadcast ext weights exactly like [`soa_fold8_base`]. Returns the
/// limb-major SoA block of the 4 folded ext values.
#[inline(always)]
pub unsafe fn lsb_soa_fold8_base(
    src: *const BabyBearField,
    prefix_limbs: &[[uint32x4_t; 4]; 8], // [tap][limb] broadcast
    blk: usize,                          // output rows 4*blk .. 4*blk+4
) -> [uint32x4_t; 4] {
    let p = (src as *const u32).add(blk * 32);
    let lo = transpose4x4(
        vld1q_u32(p),
        vld1q_u32(p.add(8)),
        vld1q_u32(p.add(16)),
        vld1q_u32(p.add(24)),
    ); // taps 0..4, lanes = rows
    let hi = transpose4x4(
        vld1q_u32(p.add(4)),
        vld1q_u32(p.add(12)),
        vld1q_u32(p.add(20)),
        vld1q_u32(p.add(28)),
    ); // taps 4..8
    let mut acc = [LazyLimb::zero(); 4];
    for i in 0..4 {
        for j in 0..4 {
            acc[j].mla(prefix_limbs[i][j], lo[i]);
        }
        if i % 2 == 1 {
            for j in 0..4 {
                acc[j].condsub();
            }
        }
    }
    for i in 0..4 {
        for j in 0..4 {
            acc[j].mla(prefix_limbs[4 + i][j], hi[i]);
        }
        if i % 2 == 1 {
            for j in 0..4 {
                acc[j].condsub();
            }
        }
    }
    core::array::from_fn(|j| acc[j].redc())
}

/// Transpose 4 AoS ext values at element stride `stride` to limb-major SoA.
#[inline(always)]
unsafe fn soa_transpose_ext4_strided(src: *const BabyBearExt4, stride: usize) -> [uint32x4_t; 4] {
    let p = src as *const u32;
    transpose4x4(
        vld1q_u32(p),
        vld1q_u32(p.add(4 * stride)),
        vld1q_u32(p.add(8 * stride)),
        vld1q_u32(p.add(12 * stride)),
    )
}

/// LSB-layout 8-tap fold of an ext poly, 4 consecutive OUTPUT rows per call:
/// per tap the 4 rows' elements (stride 8, all within the same 512-byte
/// window) are transposed to limb-major and lazy-accumulated through the
/// tap's canonical [`SoaExtTable`], exactly like [`soa_fold8_ext`].
#[inline(always)]
pub unsafe fn lsb_soa_fold8_ext(
    src: *const BabyBearExt4,
    tables: &[SoaExtTable; 8],
    blk: usize,
) -> [uint32x4_t; 4] {
    let base = src.add(blk * 32);
    let mut acc = [LazyLimb::zero(); 4];
    for i in 0..8 {
        let v = soa_transpose_ext4_strided(base.add(i), 8);
        let t = &tables[i];
        for j in 0..4 {
            acc[j].mla(t.m[j][0], v[0]);
            acc[j].mla(t.m[j][1], v[1]);
            acc[j].condsub();
            acc[j].mla(t.m[j][2], v[2]);
            acc[j].mla(t.m[j][3], v[3]);
            acc[j].condsub();
        }
    }
    core::array::from_fn(|j| acc[j].redc())
}

/// `lazy[cell] += coeff (x) (a[cell] (x) b[cell])` over N ext SoA cells with
/// the coefficient multiply DEFERRED: one full SoA ext mul for `a (x) b`
/// (canonical), then the fixed coefficient's canonical [`SoaExtTable`] rows
/// are raw-vmlal-accumulated into the u64 lane buffer (invariant `X < R*P`,
/// cond-subtract after every 2 accumulated products).
#[inline(always)]
pub unsafe fn soa_quad_ee_lazy<const N: usize>(
    lazy: *mut u64,
    a: *const u32,
    b: *const u32,
    table: &SoaExtTable,
    r11v: uint32x4_t,
) {
    for c in 0..N {
        let av = soa_load_cell(a.add(16 * c));
        let bv = soa_load_cell(b.add(16 * c));
        let v = soa_ext_mul(&av, &bv, r11v);
        for l in 0..4 {
            let p = lazy.add(16 * c + 4 * l);
            let mut acc = LazyLimb {
                lo: vld1q_u64(p),
                hi: vld1q_u64(p.add(2)),
            };
            acc.mla(table.m[l][0], v[0]);
            acc.mla(table.m[l][1], v[1]);
            acc.condsub();
            acc.mla(table.m[l][2], v[2]);
            acc.mla(table.m[l][3], v[3]);
            acc.condsub();
            vst1q_u64(p, acc.lo);
            vst1q_u64(p.add(2), acc.hi);
        }
    }
}

/// `lazy[cell] += coeff (x) a[cell]` over N ext SoA cells, fully lazy (no ext
/// multiply at all -- just the coefficient table's raw products).
#[inline(always)]
pub unsafe fn soa_lin_ext_lazy<const N: usize>(lazy: *mut u64, a: *const u32, table: &SoaExtTable) {
    for c in 0..N {
        let v = soa_load_cell(a.add(16 * c));
        for l in 0..4 {
            let p = lazy.add(16 * c + 4 * l);
            let mut acc = LazyLimb {
                lo: vld1q_u64(p),
                hi: vld1q_u64(p.add(2)),
            };
            acc.mla(table.m[l][0], v[0]);
            acc.mla(table.m[l][1], v[1]);
            acc.condsub();
            acc.mla(table.m[l][2], v[2]);
            acc.mla(table.m[l][3], v[3]);
            acc.condsub();
            vst1q_u64(p, acc.lo);
            vst1q_u64(p.add(2), acc.hi);
        }
    }
}

/// Inverse of `soa_transpose_ext4`: limb-major row vectors -> 4 AoS ext values.
#[inline(always)]
pub unsafe fn soa_store_ext4(limbs: &[uint32x4_t; 4], dst: *mut BabyBearExt4) {
    let t = transpose4x4(limbs[0], limbs[1], limbs[2], limbs[3]);
    let d = dst as *mut u32;
    vst1q_u32(d, t[0]);
    vst1q_u32(d.add(4), t[1]);
    vst1q_u32(d.add(8), t[2]);
    vst1q_u32(d.add(12), t[3]);
}

/// SoA limb-major sub over one cell: `a - b`.
#[inline(always)]
pub unsafe fn soa_sub_limbs(a: &[uint32x4_t; 4], b: &[uint32x4_t; 4]) -> [uint32x4_t; 4] {
    core::array::from_fn(|j| sub4(a[j], b[j]))
}

/// SoA limb-major add over one cell.
#[inline(always)]
pub unsafe fn soa_add_limbs(a: &[uint32x4_t; 4], b: &[uint32x4_t; 4]) -> [uint32x4_t; 4] {
    core::array::from_fn(|j| add4(a[j], b[j]))
}

/// Load one SoA cell (limb-major) from a raw grid buffer.
#[inline(always)]
pub unsafe fn soa_load_cell(src: *const u32) -> [uint32x4_t; 4] {
    core::array::from_fn(|j| vld1q_u32(src.add(4 * j)))
}

/// Store one SoA cell (limb-major) into a raw grid buffer.
#[inline(always)]
pub unsafe fn soa_store_cell(dst: *mut u32, v: &[uint32x4_t; 4]) {
    for j in 0..4 {
        vst1q_u32(dst.add(4 * j), v[j]);
    }
}

/// `dst[cell] += coeff (x) (a[cell] (x) b[cell])` over N ext SoA cells.
#[inline(always)]
pub unsafe fn soa_quad_ee_n<const N: usize>(
    dst: *mut u32,
    a: *const u32,
    b: *const u32,
    coeff_bcast: &[uint32x4_t; 4],
    r11v: uint32x4_t,
) {
    for c in 0..N {
        let av = soa_load_cell(a.add(16 * c));
        let bv = soa_load_cell(b.add(16 * c));
        let v = soa_ext_mul(&av, &bv, r11v);
        let w = soa_ext_mul(&v, coeff_bcast, r11v);
        let p = dst.add(16 * c);
        for l in 0..4 {
            let q = p.add(4 * l);
            vst1q_u32(q, add4(vld1q_u32(q), w[l]));
        }
    }
}

/// `dst[cell 0] += coeff (x) a[cell 0]` — value-cell-only linear step for the
/// transition's `[G(0), G_inf]` scratch.
#[inline(always)]
pub unsafe fn soa_lin_ext_cell0(
    dst: *mut u32,
    a: *const u32,
    coeff_bcast: &[uint32x4_t; 4],
    r11v: uint32x4_t,
) {
    let av = soa_load_cell(a);
    let w = soa_ext_mul(&av, coeff_bcast, r11v);
    for l in 0..4 {
        let q = dst.add(4 * l);
        vst1q_u32(q, add4(vld1q_u32(q), w[l]));
    }
}

/// `dst[cell 0] += constant` (broadcast limbs).
#[inline(always)]
pub unsafe fn soa_add_const_cell0(dst: *mut u32, const_bcast: &[uint32x4_t; 4]) {
    for l in 0..4 {
        let q = dst.add(4 * l);
        vst1q_u32(q, add4(vld1q_u32(q), const_bcast[l]));
    }
}

/// Per-block eq application over N cells: `acc[cell] += eval[cell] (x) eq`,
/// zeroing the eval scratch.
#[inline(always)]
pub unsafe fn soa_apply_eq_and_accumulate_n<const N: usize>(
    acc: *mut u32,
    eval: *mut u32,
    eq_soa: &[uint32x4_t; 4],
    r11v: uint32x4_t,
) {
    for c in 0..N {
        let v = soa_load_cell(eval.add(16 * c));
        let w = soa_ext_mul(&v, eq_soa, r11v);
        let p = acc.add(16 * c);
        for l in 0..4 {
            let q = p.add(4 * l);
            vst1q_u32(q, add4(vld1q_u32(q), w[l]));
            vst1q_u32(eval.add(16 * c + 4 * l), vdupq_n_u32(0));
        }
    }
}

/// Horizontal reduction of an N-cell SoA chunk accumulator to AoS ext values.
#[inline(always)]
pub unsafe fn soa_final_reduce_to_ext_n<const N: usize>(
    acc: *const u32,
    out: *mut BabyBearExt4,
) {
    for c in 0..N {
        let mut limbs = [0u32; 4];
        for l in 0..4 {
            let mut s = 0u64;
            for r in 0..4 {
                s += *acc.add(16 * c + 4 * l + r) as u64;
            }
            limbs[l] = (s % (P as u64)) as u32;
        }
        *out.add(c) = core::mem::transmute(limbs);
    }
}

/// `dst[cell] += src[cell]` over N ext SoA cells (form build, folded stages).
#[inline(always)]
pub unsafe fn soa_ext_form_add_n<const N: usize>(dst: *mut u32, src: *const u32) {
    for i in 0..(4 * N) {
        let p = dst.add(4 * i);
        vst1q_u32(p, add4(vld1q_u32(p), vld1q_u32(src.add(4 * i))));
    }
}

/// `dst[cell] -= src[cell]` over N ext SoA cells.
#[inline(always)]
pub unsafe fn soa_ext_form_sub_n<const N: usize>(dst: *mut u32, src: *const u32) {
    for i in 0..(4 * N) {
        let p = dst.add(4 * i);
        vst1q_u32(p, sub4(vld1q_u32(p), vld1q_u32(src.add(4 * i))));
    }
}

/// `dst[cell] += c * src[cell]` (base-field coefficient) over N ext SoA cells.
#[inline(always)]
pub unsafe fn soa_ext_form_muladd_n<const N: usize>(
    dst: *mut u32,
    src: *const u32,
    c: BabyBearField,
) {
    let cv = vdupq_n_u32(c.raw_u32_value());
    for i in 0..(4 * N) {
        let p = dst.add(4 * i);
        vst1q_u32(
            p,
            add4(vld1q_u32(p), mont_mul4(vld1q_u32(src.add(4 * i)), cv)),
        );
    }
}

// ---------------------------------------------------------------------------
// size-8 NTT / LDE kernels for the univariate skip (k = 3)
//
// The 8 packed values of a block live on the subgroup H = <w8>. The LDE to the
// coset g*H (g = w16, so H u gH = <w16>) is: DIF inverse-NTT (natural input,
// bit-reversed unscaled coefficients) -> diagonal multiply by g^i / 8 (stored
// in bit-reversed order, 1/8 folded in) -> DIT forward NTT (bit-reversed
// input, natural output). All twiddles are BASE-field constants, so the
// transform is lane-parallel over 4 rows and applies per limb for ext values.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
pub struct SoaLde8Tables {
    fwd: [uint32x4_t; 3],          // w8, w8^2, w8^3
    inv: [uint32x4_t; 3],          // w8^-1, w8^-2, w8^-3
    coset_scaled: [uint32x4_t; 8], // (g^i / 8) in bit-reversed positions
}

impl SoaLde8Tables {
    /// `omega8` must have multiplicative order 8; `gamma` is the coset shift
    /// (typically a 16th root of unity with `gamma^2 = omega8`).
    pub fn new(omega8: BabyBearField, gamma: BabyBearField) -> Self {
        let mut check = omega8.pow(8);
        assert!(check.is_one());
        check = omega8.pow(4);
        assert!(!check.is_one());

        let b = |v: BabyBearField| unsafe { vdupq_n_u32(v.raw_u32_value()) };
        let winv = omega8.inverse().expect("root invertible");
        let eighth = BabyBearField::from_u32_with_reduction(8)
            .inverse()
            .expect("8 invertible");
        let bitrev = [0usize, 4, 2, 6, 1, 5, 3, 7];
        let mut coset = [BabyBearField::ZERO; 8];
        for i in 0..8 {
            let mut t = gamma.pow(i as u32);
            t.mul_assign(&eighth);
            coset[bitrev[i]] = t;
        }
        SoaLde8Tables {
            fwd: [b(omega8), b(omega8.pow(2)), b(omega8.pow(3))],
            inv: [b(winv), b(winv.pow(2)), b(winv.pow(3))],
            coset_scaled: core::array::from_fn(|i| b(coset[i])),
        }
    }
}

/// DIF NTT stage structure: natural input, bit-reversed output; twiddles are
/// applied to the difference. `w[0..3]` are the 1st..3rd powers of the root.
#[inline(always)]
unsafe fn soa_ntt8_dif(x: &mut [uint32x4_t; 8], w: &[uint32x4_t; 3]) {
    // stage distance 4: (x_j, x_{j+4}) -> (x_j + x_{j+4}, (x_j - x_{j+4}) * w^j)
    for j in 0..4 {
        let a = x[j];
        let bb = x[j + 4];
        x[j] = add4(a, bb);
        let d = sub4(a, bb);
        x[j + 4] = if j == 0 { d } else { mont_mul4(d, w[j - 1]) };
    }
    // stage distance 2 (per half): twiddles w^0, w^2
    for base in [0usize, 4] {
        for j in 0..2 {
            let a = x[base + j];
            let bb = x[base + j + 2];
            x[base + j] = add4(a, bb);
            let d = sub4(a, bb);
            x[base + j + 2] = if j == 0 { d } else { mont_mul4(d, w[1]) };
        }
    }
    // stage distance 1
    for base in [0usize, 2, 4, 6] {
        let a = x[base];
        let bb = x[base + 1];
        x[base] = add4(a, bb);
        x[base + 1] = sub4(a, bb);
    }
}

/// DIT NTT: bit-reversed input, natural output; twiddles applied to the
/// second operand before the butterfly.
#[inline(always)]
unsafe fn soa_ntt8_dit(x: &mut [uint32x4_t; 8], w: &[uint32x4_t; 3]) {
    for base in [0usize, 2, 4, 6] {
        let a = x[base];
        let bb = x[base + 1];
        x[base] = add4(a, bb);
        x[base + 1] = sub4(a, bb);
    }
    for base in [0usize, 4] {
        for j in 0..2 {
            let a = x[base + j];
            let t = if j == 0 {
                x[base + j + 2]
            } else {
                mont_mul4(x[base + j + 2], w[1])
            };
            x[base + j] = add4(a, t);
            x[base + j + 2] = sub4(a, t);
        }
    }
    for j in 0..4 {
        let a = x[j];
        let t = if j == 0 {
            x[j + 4]
        } else {
            mont_mul4(x[j + 4], w[j - 1])
        };
        x[j] = add4(a, t);
        x[j + 4] = sub4(a, t);
    }
}

/// LDE of one 8-cell SoA block: values on H (natural order, 4 rows/lane) ->
/// values on the coset g*H (natural order).
#[inline(always)]
pub unsafe fn soa_lde8(cells: &[uint32x4_t; 8], t: &SoaLde8Tables) -> [uint32x4_t; 8] {
    let mut x = *cells;
    soa_ntt8_dif(&mut x, &t.inv);
    for i in 0..8 {
        x[i] = mont_mul4(x[i], t.coset_scaled[i]);
    }
    soa_ntt8_dit(&mut x, &t.fwd);
    x
}

/// Read the 8 packed values of a base poly for rows `row..row+4` in domain
/// order j = 4*x0 + 2*x1 + x2 (top-bit strides), one vld1q per tap.
#[inline(always)]
pub unsafe fn soa_read_base_block8(
    src: *const BabyBearField,
    input_size: usize,
    row: usize,
) -> [uint32x4_t; 8] {
    let src = src as *const u32;
    let s0 = input_size / 2;
    let s1 = input_size / 4;
    let s2 = input_size / 8;
    core::array::from_fn(|j| {
        vld1q_u32(src.add(row + (j >> 2) * s0 + ((j >> 1) & 1) * s1 + (j & 1) * s2))
    })
}

/// `acc[cell] += coeff * a[cell]` over ALL N cells (packed linear terms are
/// dense over the evaluation domain), lazily.
#[inline(always)]
pub unsafe fn soa_lin_base_all_n<const N: usize>(
    acc: *mut u64,
    a: *const u32,
    coeff: &BabyBearExt4,
) {
    let climbs: [u32; 4] = core::mem::transmute(*coeff);
    for c in 0..N {
        let t = vld1q_u32(a.add(4 * c));
        let t_lo = vget_low_u32(t);
        for l in 0..4 {
            let p = acc.add(16 * c + 4 * l);
            let cl = climbs[l];
            let lo = vmlal_u32(vld1q_u64(p), t_lo, vdup_n_u32(cl));
            let hi = vmlal_high_u32(vld1q_u64(p.add(2)), t, vdupq_n_u32(cl));
            vst1q_u64(p, lo);
            vst1q_u64(p.add(2), hi);
        }
    }
}

/// `dst[cell] += coeff (x) a_ext[cell]` over ALL N cells (reduced path).
#[inline(always)]
pub unsafe fn soa_lin_ext_all_n<const N: usize>(
    dst: *mut u32,
    a_ext: *const u32,
    coeff_bcast: &[uint32x4_t; 4],
    r11v: uint32x4_t,
) {
    for c in 0..N {
        let av: [uint32x4_t; 4] = core::array::from_fn(|l| vld1q_u32(a_ext.add(16 * c + 4 * l)));
        let w = soa_ext_mul(&av, coeff_bcast, r11v);
        for l in 0..4 {
            let p = dst.add(16 * c + 4 * l);
            vst1q_u32(p, add4(vld1q_u32(p), w[l]));
        }
    }
}

/// `dst[cell] += constant` over ALL N cells (reduced path).
#[inline(always)]
pub unsafe fn soa_add_const_all_n<const N: usize>(dst: *mut u32, const_bcast: &[uint32x4_t; 4]) {
    for c in 0..N {
        for l in 0..4 {
            let p = dst.add(16 * c + 4 * l);
            vst1q_u32(p, add4(vld1q_u32(p), const_bcast[l]));
        }
    }
}

/// Base-grid form ops over N SoA cells (bracket materialization on H).
#[inline(always)]
pub unsafe fn soa_base_form_add_n<const N: usize>(dst: *mut u32, src: *const u32) {
    for i in 0..N {
        let p = dst.add(4 * i);
        vst1q_u32(p, add4(vld1q_u32(p), vld1q_u32(src.add(4 * i))));
    }
}

#[inline(always)]
pub unsafe fn soa_base_form_sub_n<const N: usize>(dst: *mut u32, src: *const u32) {
    for i in 0..N {
        let p = dst.add(4 * i);
        vst1q_u32(p, sub4(vld1q_u32(p), vld1q_u32(src.add(4 * i))));
    }
}

#[inline(always)]
pub unsafe fn soa_base_form_muladd_n<const N: usize>(
    dst: *mut u32,
    src: *const u32,
    c: BabyBearField,
) {
    let cv = vdupq_n_u32(c.raw_u32_value());
    for i in 0..N {
        let p = dst.add(4 * i);
        vst1q_u32(
            p,
            add4(vld1q_u32(p), mont_mul4(vld1q_u32(src.add(4 * i)), cv)),
        );
    }
}

// ---------------------------------------------------------------------------
// size-64 NTT / LDE kernels for the univariate skip (k = 6)
//
// Two interchangeable transforms (bit-identical results):
// * radix-2: 6 unrolled stages over the 64-vector scratch (DIF natural ->
//   bit-reversed, DIT back), twiddles w64^j;
// * radix-8: two rounds of the register-resident 8-point kernel (columns then
//   rows of the 8x8 matrix view) with an inter-round twiddle table
//   W[i0][k0] = w64^(i0*k0); intermediate order is digit-swapped (8a+b <-> 8b+a)
//   instead of bit-reversed.
// The coset diagonal (gamma^i / 64) is stored in the matching permuted order
// so the IFFT -> diagonal -> FFT pipeline needs no explicit reordering.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
pub struct SoaLde64Tables {
    // radix-2 path
    w_fwd: [uint32x4_t; 32], // w64^j
    w_inv: [uint32x4_t; 32],
    coset_bitrev: [uint32x4_t; 64], // gamma^i / 64 at bitrev6(i)
    // radix-8 path
    w8_fwd: [uint32x4_t; 3], // (w64^8)^1..3
    w8_inv: [uint32x4_t; 3],
    inter_fwd: [uint32x4_t; 64], // w64^(i0*k0) at 8*i0+k0
    inter_inv: [uint32x4_t; 64],
    coset_digitrev: [uint32x4_t; 64], // gamma^(8a+b) / 64 at 8b+a
}

fn bitrev6(i: usize) -> usize {
    ((i & 1) << 5) | ((i & 2) << 3) | ((i & 4) << 1) | ((i & 8) >> 1) | ((i & 16) >> 3) | ((i & 32) >> 5)
}

impl SoaLde64Tables {
    /// `omega64` must have order 64; `gamma` is the coset shift (typically a
    /// 128th root with `gamma^2 = omega64`).
    pub fn new(omega64: BabyBearField, gamma: BabyBearField) -> Self {
        assert!(omega64.pow(64).is_one());
        assert!(!omega64.pow(32).is_one());
        let b = |v: BabyBearField| unsafe { vdupq_n_u32(v.raw_u32_value()) };
        let winv = omega64.inverse().expect("invertible");
        let w8 = omega64.pow(8);
        let w8i = winv.pow(8);
        let inv64 = BabyBearField::from_u32_with_reduction(64)
            .inverse()
            .expect("64 invertible");

        let mut coset_bitrev = [BabyBearField::ZERO; 64];
        let mut coset_digitrev = [BabyBearField::ZERO; 64];
        for i in 0..64usize {
            let mut t = gamma.pow(i as u32);
            t.mul_assign(&inv64);
            coset_bitrev[bitrev6(i)] = t;
            let (a, bb) = (i / 8, i % 8);
            coset_digitrev[8 * bb + a] = t;
        }
        let mut inter_fwd = [BabyBearField::ZERO; 64];
        let mut inter_inv = [BabyBearField::ZERO; 64];
        for i0 in 0..8usize {
            for k0 in 0..8usize {
                inter_fwd[8 * i0 + k0] = omega64.pow((i0 * k0) as u32);
                inter_inv[8 * i0 + k0] = winv.pow((i0 * k0) as u32);
            }
        }
        SoaLde64Tables {
            w_fwd: core::array::from_fn(|j| b(omega64.pow(j as u32))),
            w_inv: core::array::from_fn(|j| b(winv.pow(j as u32))),
            coset_bitrev: core::array::from_fn(|i| b(coset_bitrev[i])),
            w8_fwd: [b(w8), b(w8.pow(2)), b(w8.pow(3))],
            w8_inv: [b(w8i), b(w8i.pow(2)), b(w8i.pow(3))],
            inter_fwd: core::array::from_fn(|i| b(inter_fwd[i])),
            inter_inv: core::array::from_fn(|i| b(inter_inv[i])),
            coset_digitrev: core::array::from_fn(|i| b(coset_digitrev[i])),
        }
    }
}

/// radix-2 DIF, natural input -> bit-reversed output.
#[inline(always)]
unsafe fn soa_ntt64_dif_r2(x: &mut [uint32x4_t; 64], w: &[uint32x4_t; 32]) {
    let mut dist = 32usize;
    while dist >= 1 {
        let step = 32 / dist;
        let mut base = 0usize;
        while base < 64 {
            for j in 0..dist {
                let a = x[base + j];
                let c = x[base + j + dist];
                x[base + j] = add4(a, c);
                let d = sub4(a, c);
                x[base + j + dist] = if j == 0 { d } else { mont_mul4(d, w[j * step]) };
            }
            base += 2 * dist;
        }
        dist /= 2;
    }
}

/// radix-2 DIT, bit-reversed input -> natural output.
#[inline(always)]
unsafe fn soa_ntt64_dit_r2(x: &mut [uint32x4_t; 64], w: &[uint32x4_t; 32]) {
    let mut dist = 1usize;
    while dist <= 32 {
        let step = 32 / dist;
        let mut base = 0usize;
        while base < 64 {
            for j in 0..dist {
                let a = x[base + j];
                let t = if j == 0 {
                    x[base + j + dist]
                } else {
                    mont_mul4(x[base + j + dist], w[j * step])
                };
                x[base + j] = add4(a, t);
                x[base + j + dist] = sub4(a, t);
            }
            base += 2 * dist;
        }
        dist *= 2;
    }
}

/// natural-order 8-point NTT (DIF + the two bit-reversal swaps).
#[inline(always)]
unsafe fn soa_ntt8_natural(x: &mut [uint32x4_t; 8], w: &[uint32x4_t; 3]) {
    soa_ntt8_dif(x, w);
    x.swap(1, 4);
    x.swap(3, 6);
}

/// radix-8 two-round transform, natural input -> digit-swapped output
/// (position 8*k0+k1 holds output index 8*k1+k0).
#[inline(always)]
unsafe fn soa_ntt64_r8_nat_to_digitrev(
    x: &mut [uint32x4_t; 64],
    w8: &[uint32x4_t; 3],
    inter: &[uint32x4_t; 64],
) {
    let mut buf = [vdupq_n_u32(0); 64];
    for i0 in 0..8 {
        let mut tmp: [uint32x4_t; 8] = core::array::from_fn(|a| x[8 * a + i0]);
        soa_ntt8_natural(&mut tmp, w8);
        for k0 in 0..8 {
            buf[8 * i0 + k0] = if i0 == 0 || k0 == 0 {
                tmp[k0]
            } else {
                mont_mul4(tmp[k0], inter[8 * i0 + k0])
            };
        }
    }
    for k0 in 0..8 {
        let mut tmp: [uint32x4_t; 8] = core::array::from_fn(|i0| buf[8 * i0 + k0]);
        soa_ntt8_natural(&mut tmp, w8);
        for k1 in 0..8 {
            x[8 * k0 + k1] = tmp[k1];
        }
    }
}

/// radix-8 two-round transform, digit-swapped input -> natural output.
#[inline(always)]
unsafe fn soa_ntt64_r8_digitrev_to_nat(
    x: &mut [uint32x4_t; 64],
    w8: &[uint32x4_t; 3],
    inter: &[uint32x4_t; 64],
) {
    let mut buf = [vdupq_n_u32(0); 64];
    for i0 in 0..8 {
        // coeff index 8a+i0 is stored at 8*i0+a: contiguous row gather
        let mut tmp: [uint32x4_t; 8] = core::array::from_fn(|a| x[8 * i0 + a]);
        soa_ntt8_natural(&mut tmp, w8);
        for k0 in 0..8 {
            buf[8 * i0 + k0] = if i0 == 0 || k0 == 0 {
                tmp[k0]
            } else {
                mont_mul4(tmp[k0], inter[8 * i0 + k0])
            };
        }
    }
    for k0 in 0..8 {
        let mut tmp: [uint32x4_t; 8] = core::array::from_fn(|i0| buf[8 * i0 + k0]);
        soa_ntt8_natural(&mut tmp, w8);
        for k1 in 0..8 {
            x[8 * k1 + k0] = tmp[k1];
        }
    }
}

/// size-64 LDE, radix-2 pipeline: H values (natural) -> coset gamma*H values
/// (natural).
#[inline(always)]
pub unsafe fn soa_lde64_r2(cells: &[uint32x4_t; 64], t: &SoaLde64Tables) -> [uint32x4_t; 64] {
    let mut x = *cells;
    soa_ntt64_dif_r2(&mut x, &t.w_inv);
    for i in 0..64 {
        x[i] = mont_mul4(x[i], t.coset_bitrev[i]);
    }
    soa_ntt64_dit_r2(&mut x, &t.w_fwd);
    x
}

/// size-64 LDE, radix-8 pipeline (bit-identical to `soa_lde64_r2`).
#[inline(always)]
pub unsafe fn soa_lde64_r8(cells: &[uint32x4_t; 64], t: &SoaLde64Tables) -> [uint32x4_t; 64] {
    let mut x = *cells;
    soa_ntt64_r8_nat_to_digitrev(&mut x, &t.w8_inv, &t.inter_inv);
    for i in 0..64 {
        x[i] = mont_mul4(x[i], t.coset_digitrev[i]);
    }
    soa_ntt64_r8_digitrev_to_nat(&mut x, &t.w8_fwd, &t.inter_fwd);
    x
}

/// Read the 64 packed values of a base poly for rows `row..row+4` in domain
/// order (6-bit index, top-bit strides).
#[inline(always)]
pub unsafe fn soa_read_base_block64(
    src: *const BabyBearField,
    input_size: usize,
    row: usize,
) -> [uint32x4_t; 64] {
    let src = src as *const u32;
    let s = input_size / 64;
    core::array::from_fn(|j| {
        // j = b5..b0 with b5 the top trace bit: offset = sum b_i * (input/2^(6-i))
        let mut off = row;
        for bit in 0..6 {
            if (j >> bit) & 1 == 1 {
                off += s << bit;
            }
        }
        vld1q_u32(src.add(off))
    })
}

/// Broadcast limb vectors for the fold prefix of base polys.
#[inline(always)]
pub fn soa_prefix_limbs(prefix: &[BabyBearExt4; 8]) -> [[uint32x4_t; 4]; 8] {
    core::array::from_fn(|i| {
        let l: [u32; 4] = unsafe { core::mem::transmute(prefix[i]) };
        core::array::from_fn(|j| unsafe { vdupq_n_u32(l[j]) })
    })
}

/// `dst[cell] += src[cell]` over the full 27x4 SoA base grid (form build).
#[inline(always)]
pub unsafe fn soa_form_add(dst: *mut u32, src: *const u32) {
    for i in 0..27 {
        let p = dst.add(4 * i);
        vst1q_u32(p, add4(vld1q_u32(p), vld1q_u32(src.add(4 * i))));
    }
}

/// `dst[cell] -= src[cell]` over the full 27x4 SoA base grid.
#[inline(always)]
pub unsafe fn soa_form_sub(dst: *mut u32, src: *const u32) {
    for i in 0..27 {
        let p = dst.add(4 * i);
        vst1q_u32(p, sub4(vld1q_u32(p), vld1q_u32(src.add(4 * i))));
    }
}

/// `dst[cell] += c * src[cell]` over the full 27x4 SoA base grid.
#[inline(always)]
pub unsafe fn soa_form_muladd(dst: *mut u32, src: *const u32, c: BabyBearField) {
    let cv = vdupq_n_u32(c.raw_u32_value());
    for i in 0..27 {
        let p = dst.add(4 * i);
        vst1q_u32(
            p,
            add4(vld1q_u32(p), mont_mul4(vld1q_u32(src.add(4 * i)), cv)),
        );
    }
}

/// Horizontal reduction of the chunk accumulator: sum the 4 row lanes of every
/// (cell, limb) and write AoS ext cells.
#[inline(always)]
pub unsafe fn soa_final_reduce_to_ext(acc: *const u32, out: *mut BabyBearExt4) {
    for c in 0..27 {
        let mut limbs = [0u32; 4];
        for l in 0..4 {
            let mut s = 0u64;
            for r in 0..4 {
                s += *acc.add(16 * c + 4 * l + r) as u64;
            }
            limbs[l] = (s % (P as u64)) as u32;
        }
        *out.add(c) = core::mem::transmute(limbs);
    }
}

/// Inverse of [`soa_transpose_ext4`] over N SoA cell-groups: limb-major SoA
/// (lanes = 4 consecutive cells) back to 4N contiguous AoS ext values.
#[inline(always)]
pub unsafe fn soa_untranspose_to_aos_ext<const N: usize>(acc: *const u32, out: *mut BabyBearExt4) {
    for g in 0..N {
        let t = transpose4x4(
            vld1q_u32(acc.add(16 * g)),
            vld1q_u32(acc.add(16 * g + 4)),
            vld1q_u32(acc.add(16 * g + 8)),
            vld1q_u32(acc.add(16 * g + 12)),
        );
        let p = out.add(4 * g) as *mut u32;
        for e in 0..4 {
            vst1q_u32(p.add(4 * e), t[e]);
        }
    }
}

// ---------------------------------------------------------------------------
// LSB-layout ("contiguous tap") kernels: the window variables are the LOW bits
// of the trace index, so one row's 2^k packed values are contiguous in memory
// and one call processes ONE row -- 4 CELLS per vector for base values (the
// in-register NTT needs shuffle stages for butterfly distances 2 and 1), one
// ext element per vector (`soa_lde8` / `soa_lde64_r2` apply unchanged: their
// per-vector lanes are independent, and broadcast base twiddles times a
// [4-limb ext element] vector IS the ext-by-base product). Used only by the
// artificial LSB-binding bench (`lsb_bench`).
// ---------------------------------------------------------------------------

/// In-vector DIF tail: butterfly distances 2 then 1 on the 4 cells of one
/// vector, standard in-place positions. `tw2 = [1, 1, 1, w^(n/4)]` applies the
/// distance-2 stage's only non-unit twiddle after packing.
#[inline(always)]
unsafe fn lsb_dif_tail(v: uint32x4_t, tw2: uint32x4_t) -> uint32x4_t {
    // distance 2: pairs (0,2),(1,3) -> [s0, s1, d0, d1] then diagonal twiddle
    let hi = vextq_u32(v, v, 2);
    let s = add4(v, hi);
    let d = sub4(v, hi);
    let packed = vreinterpretq_u32_u64(vzip1q_u64(
        vreinterpretq_u64_u32(s),
        vreinterpretq_u64_u32(d),
    ));
    let v = mont_mul4(packed, tw2);
    // distance 1: pairs (0,1),(2,3), twiddle 1
    let r = vrev64q_u32(v);
    let s = add4(v, r);
    let d = sub4(v, r);
    vtrn1q_u32(s, d)
}

/// In-vector DIT head: the mirror of [`lsb_dif_tail`] (distance 1 then 2,
/// twiddle applied to the second operand before the butterfly).
#[inline(always)]
unsafe fn lsb_dit_head(v: uint32x4_t, tw2: uint32x4_t) -> uint32x4_t {
    let r = vrev64q_u32(v);
    let s = add4(v, r);
    let d = sub4(v, r);
    let v = vtrn1q_u32(s, d);
    let v = mont_mul4(v, tw2);
    let hi = vextq_u32(v, v, 2);
    let s = add4(v, hi);
    let d = sub4(v, hi);
    vreinterpretq_u32_u64(vzip1q_u64(
        vreinterpretq_u64_u32(s),
        vreinterpretq_u64_u32(d),
    ))
}

#[derive(Clone, Copy)]
pub struct LsbLde8Tables {
    inv_d4: uint32x4_t,  // lanes [1, wi, wi^2, wi^3]
    inv_tw2: uint32x4_t, // [1, 1, 1, wi^2]
    fwd_d4: uint32x4_t,
    fwd_tw2: uint32x4_t,
    scale: [uint32x4_t; 2], // gamma^bitrev3(p) / 8, packed 4 positions/vector
}

impl LsbLde8Tables {
    pub fn new(omega8: BabyBearField, gamma: BabyBearField) -> Self {
        assert!(omega8.pow(8).is_one());
        assert!(!omega8.pow(4).is_one());
        let lanes = |a: [BabyBearField; 4]| unsafe {
            let raw = [
                a[0].raw_u32_value(),
                a[1].raw_u32_value(),
                a[2].raw_u32_value(),
                a[3].raw_u32_value(),
            ];
            vld1q_u32(raw.as_ptr())
        };
        let one = BabyBearField::ONE;
        let wi = omega8.inverse().expect("invertible");
        let eighth = BabyBearField::from_u32_with_reduction(8)
            .inverse()
            .expect("8 invertible");
        let bitrev3 = [0usize, 4, 2, 6, 1, 5, 3, 7];
        let mut scale = [BabyBearField::ZERO; 8];
        for m in 0..8 {
            let mut t = gamma.pow(m as u32);
            t.mul_assign(&eighth);
            scale[bitrev3[m]] = t;
        }
        LsbLde8Tables {
            inv_d4: lanes([one, wi, wi.pow(2), wi.pow(3)]),
            inv_tw2: lanes([one, one, one, wi.pow(2)]),
            fwd_d4: lanes([one, omega8, omega8.pow(2), omega8.pow(3)]),
            fwd_tw2: lanes([one, one, one, omega8.pow(2)]),
            scale: [
                lanes([scale[0], scale[1], scale[2], scale[3]]),
                lanes([scale[4], scale[5], scale[6], scale[7]]),
            ],
        }
    }
}

/// LDE of one row's 8 contiguous cells (2 vectors, 4 cells/lane-group):
/// values on H (natural order) -> values on the coset gamma*H (natural order).
#[inline(always)]
pub unsafe fn lsb_lde8_base(h: [uint32x4_t; 2], t: &LsbLde8Tables) -> [uint32x4_t; 2] {
    // DIF inverse NTT: cross-vector distance 4, then in-vector tail
    let s = add4(h[0], h[1]);
    let d = mont_mul4(sub4(h[0], h[1]), t.inv_d4);
    let mut v0 = lsb_dif_tail(s, t.inv_tw2);
    let mut v1 = lsb_dif_tail(d, t.inv_tw2);
    // coset + 1/8 diagonal in bit-reversed positions
    v0 = mont_mul4(v0, t.scale[0]);
    v1 = mont_mul4(v1, t.scale[1]);
    // DIT forward NTT
    let v0 = lsb_dit_head(v0, t.fwd_tw2);
    let v1 = lsb_dit_head(v1, t.fwd_tw2);
    let tt = mont_mul4(v1, t.fwd_d4);
    [add4(v0, tt), sub4(v0, tt)]
}

// ---- partially-reduced (u32-lazy) variant of the size-8 LDE ----
//
// Values live in [0, 2P) between operations. With BabyBear (P ~ 2^30.9) a sum
// of two operands only fits u32 when both are < P (2P < 2^32 < 3P), so the
// butterfly add/sub REQUIRE canonical inputs; everything else is deferred:
// * Montgomery multiply drops its final conditional subtraction -- REDC alone
//   returns < 2P, and its input bound holds for a lazy operand times a
//   canonical twiddle (2P * P < R*P);
// * a value is brought back to [0, P) with ONE conditional subtraction of P
//   (`red2p`, the min trick) only right before it enters a butterfly;
// * the subtract side of a butterfly is computed as `(a + P) - b` on
//   canonical a, b -- in (0, 2P), no conditional needed.
// A wider range (conditionally subtracting 2P instead) is impossible here:
// 4P > 2^32, so [0, 2P) is already the maximal partially-reduced window.

/// `[0, 2P) -> [0, P)`: one conditional subtraction of P.
#[inline(always)]
unsafe fn red2p(v: uint32x4_t, p: uint32x4_t) -> uint32x4_t {
    vminq_u32(v, vsubq_u32(v, p))
}

/// Montgomery multiply WITHOUT the final conditional subtraction: for
/// `a < 2P`, `b < P` the REDC input `a*b + m*P < 2P^2 + R*P < 2R*P` never
/// overflows u64 and the result is `< 2P`.
#[inline(always)]
unsafe fn mont_mul4_lazy(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    let p = vdupq_n_u32(P);
    let k = vdupq_n_u32(K);
    let prod_lo = vmull_u32(vget_low_u32(a), vget_low_u32(b));
    let prod_hi = vmull_high_u32(a, b);
    let lo32 = vcombine_u32(vmovn_u64(prod_lo), vmovn_u64(prod_hi));
    let m = vmulq_u32(lo32, k);
    let prod_lo = vmlal_u32(prod_lo, vget_low_u32(m), vget_low_u32(p));
    let prod_hi = vmlal_high_u32(prod_hi, m, p);
    vcombine_u32(vshrn_n_u64::<32>(prod_lo), vshrn_n_u64::<32>(prod_hi))
}

/// Lazy in-vector DIF tail: input `< 2P`, output `< 2P`.
#[inline(always)]
unsafe fn lsb_dif_tail_lazy(v: uint32x4_t, tw2: uint32x4_t, p: uint32x4_t) -> uint32x4_t {
    // distance 2: reduce once, then raw butterflies
    let v = red2p(v, p);
    let hi = vextq_u32(v, v, 2);
    let s = vaddq_u32(v, hi); // lanes 0,1: < 2P
    let d = vsubq_u32(vaddq_u32(v, p), hi); // lanes 0,1: in (0, 2P)
    let packed = vreinterpretq_u32_u64(vzip1q_u64(
        vreinterpretq_u64_u32(s),
        vreinterpretq_u64_u32(d),
    ));
    let v = mont_mul4_lazy(packed, tw2); // < 2P
    // distance 1
    let v = red2p(v, p);
    let r = vrev64q_u32(v);
    let s = vaddq_u32(v, r);
    let d = vsubq_u32(vaddq_u32(v, p), r);
    vtrn1q_u32(s, d) // < 2P
}

/// Lazy in-vector DIT head: input `< 2P`, output `< 2P`.
#[inline(always)]
unsafe fn lsb_dit_head_lazy(v: uint32x4_t, tw2: uint32x4_t, p: uint32x4_t) -> uint32x4_t {
    let v = red2p(v, p);
    let r = vrev64q_u32(v);
    let s = vaddq_u32(v, r);
    let d = vsubq_u32(vaddq_u32(v, p), r);
    let v = vtrn1q_u32(s, d); // < 2P
    let v = mont_mul4_lazy(v, tw2); // < 2P
    let v = red2p(v, p);
    let hi = vextq_u32(v, v, 2);
    let s = vaddq_u32(v, hi);
    let d = vsubq_u32(vaddq_u32(v, p), hi);
    vreinterpretq_u32_u64(vzip1q_u64(
        vreinterpretq_u64_u32(s),
        vreinterpretq_u64_u32(d),
    ))
}

/// Partially-reduced [`lsb_lde8_base`]: canonical input and output, `[0, 2P)`
/// internally with reductions only at butterfly entry.
#[inline(always)]
pub unsafe fn lsb_lde8_base_lazy(h: [uint32x4_t; 2], t: &LsbLde8Tables) -> [uint32x4_t; 2] {
    let p = vdupq_n_u32(P);
    // DIF distance 4 on canonical inputs: raw butterflies
    let s = vaddq_u32(h[0], h[1]); // < 2P
    let d = vsubq_u32(vaddq_u32(h[0], p), h[1]); // in (0, 2P)
    let d = mont_mul4_lazy(d, t.inv_d4); // < 2P
    let v0 = lsb_dif_tail_lazy(s, t.inv_tw2, p);
    let v1 = lsb_dif_tail_lazy(d, t.inv_tw2, p);
    // coset + 1/8 diagonal
    let v0 = mont_mul4_lazy(v0, t.scale[0]);
    let v1 = mont_mul4_lazy(v1, t.scale[1]);
    // DIT
    let v0 = lsb_dit_head_lazy(v0, t.fwd_tw2, p);
    let v1 = lsb_dit_head_lazy(v1, t.fwd_tw2, p);
    let a = red2p(v0, p);
    let tt = red2p(mont_mul4_lazy(v1, t.fwd_d4), p);
    // final butterflies canonicalize the outputs
    let out0 = red2p(vaddq_u32(a, tt), p);
    let out1 = red2p(vsubq_u32(vaddq_u32(a, p), tt), p);
    [out0, out1]
}

// ---- Lagrange-matrix variant of the size-8 LDE ----
//
// For a small domain the coset LDE is just an 8x8 matrix: precompute
// M[i][j] = L_j(gamma * omega^i) (the LDE of every Lagrange basis poly), and
// the coset values are 8 dot products -- 64 scalar MACs. Vectorized over the
// LSB cell layout that is 32 fused `vmlal` widening multiply-accumulates into
// four independent u64 lane accumulators: products are canonical * canonical
// (< P^2), so the lazy R*P invariant applies (cond-subtract after products
// 4 and 6: 2P^2 < R*P, and R*P + 2P^2 < 2^64), with a single REDC +
// canonicalization per output vector at the end. No shuffles, no stage
// dependencies -- near-perfect ILP and locality.

#[derive(Clone, Copy)]
pub struct LsbLde8MatTables {
    /// column j: `[M[0..4][j], M[4..8][j]]`, canonical Montgomery form
    cols: [[uint32x4_t; 2]; 8],
}

impl LsbLde8MatTables {
    pub fn new(omega8: BabyBearField, gamma: BabyBearField) -> Self {
        assert!(omega8.pow(8).is_one());
        assert!(!omega8.pow(4).is_one());
        let winv = omega8.inverse().expect("invertible");
        let eighth = BabyBearField::from_u32_with_reduction(8)
            .inverse()
            .expect("8 invertible");
        // M[i][j] = L_j(gamma * omega^i) = (1/8) * sum_m omega^{-jm} x_i^m
        let mut m = [[BabyBearField::ZERO; 8]; 8];
        for i in 0..8usize {
            let mut x = gamma;
            x.mul_assign(&omega8.pow(i as u32));
            for j in 0..8usize {
                let mut acc = BabyBearField::ZERO;
                let mut xm = BabyBearField::ONE;
                for mm in 0..8usize {
                    let mut t = winv.pow((j * mm % 8) as u32);
                    t.mul_assign(&xm);
                    acc.add_assign(&t);
                    xm.mul_assign(&x);
                }
                acc.mul_assign(&eighth);
                m[i][j] = acc;
            }
        }
        let lanes = |a: [BabyBearField; 4]| unsafe {
            let raw = [
                a[0].raw_u32_value(),
                a[1].raw_u32_value(),
                a[2].raw_u32_value(),
                a[3].raw_u32_value(),
            ];
            vld1q_u32(raw.as_ptr())
        };
        LsbLde8MatTables {
            cols: core::array::from_fn(|j| {
                [
                    lanes([m[0][j], m[1][j], m[2][j], m[3][j]]),
                    lanes([m[4][j], m[5][j], m[6][j], m[7][j]]),
                ]
            }),
        }
    }
}

/// One REDC + canonicalization of a (lo, hi) u64 lane-accumulator pair
/// (inputs `< R*P`) into a canonical u32 vector.
#[inline(always)]
unsafe fn lazy_redc_pair(lo: uint64x2_t, hi: uint64x2_t) -> uint32x4_t {
    let p2 = vdup_n_u32(P);
    let k2 = vdup_n_u32(K);
    let pq = vdupq_n_u32(P);
    let m_lo = vmul_u32(vmovn_u64(lo), k2);
    let m_hi = vmul_u32(vmovn_u64(hi), k2);
    let lo = vmlal_u32(lo, m_lo, p2);
    let hi = vmlal_u32(hi, m_hi, p2);
    let r = vcombine_u32(vshrn_n_u64::<32>(lo), vshrn_n_u64::<32>(hi));
    vminq_u32(r, vsubq_u32(r, pq))
}

/// Lagrange-matrix [`lsb_lde8_base`]: canonical input and output.
#[inline(always)]
pub unsafe fn lsb_lde8_base_mat(h: [uint32x4_t; 2], t: &LsbLde8MatTables) -> [uint32x4_t; 2] {
    let rp = vdupq_n_u64(RP);
    let mut a0 = vdupq_n_u64(0); // coset points 0-1
    let mut a1 = vdupq_n_u64(0); // coset points 2-3
    let mut a2 = vdupq_n_u64(0); // coset points 4-5
    let mut a3 = vdupq_n_u64(0); // coset points 6-7
    macro_rules! step {
        ($hv:expr, $lane:literal, $j:literal) => {
            let hq = vdupq_laneq_u32::<$lane>($hv);
            let c0 = t.cols[$j][0];
            let c1 = t.cols[$j][1];
            a0 = vmlal_u32(a0, vget_low_u32(c0), vget_low_u32(hq));
            a1 = vmlal_high_u32(a1, c0, hq);
            a2 = vmlal_u32(a2, vget_low_u32(c1), vget_low_u32(hq));
            a3 = vmlal_high_u32(a3, c1, hq);
        };
    }
    macro_rules! condsub {
        () => {
            a0 = vsubq_u64(a0, vandq_u64(vcgeq_u64(a0, rp), rp));
            a1 = vsubq_u64(a1, vandq_u64(vcgeq_u64(a1, rp), rp));
            a2 = vsubq_u64(a2, vandq_u64(vcgeq_u64(a2, rp), rp));
            a3 = vsubq_u64(a3, vandq_u64(vcgeq_u64(a3, rp), rp));
        };
    }
    step!(h[0], 0, 0);
    step!(h[0], 1, 1);
    step!(h[0], 2, 2);
    step!(h[0], 3, 3);
    // 4 products: < 4P^2; one cond-sub restores X < R*P
    condsub!();
    step!(h[1], 0, 4);
    step!(h[1], 1, 5);
    condsub!();
    step!(h[1], 2, 6);
    step!(h[1], 3, 7);
    condsub!();
    [lazy_redc_pair(a0, a1), lazy_redc_pair(a2, a3)]
}

#[derive(Clone, Copy)]
pub struct LsbLde64Tables {
    inv_d32: [uint32x4_t; 8], // lanes wi^(4m+lane)
    inv_d16: [uint32x4_t; 4], // wi^(2*(4m+lane))
    inv_d8: [uint32x4_t; 2],  // wi^(4*(4m+lane))
    inv_d4: uint32x4_t,       // [1, wi^8, wi^16, wi^24]
    inv_tw2: uint32x4_t,      // [1, 1, 1, wi^16]
    fwd_d32: [uint32x4_t; 8],
    fwd_d16: [uint32x4_t; 4],
    fwd_d8: [uint32x4_t; 2],
    fwd_d4: uint32x4_t,
    fwd_tw2: uint32x4_t,
    scale: [uint32x4_t; 16], // gamma^bitrev6(p) / 64, packed 4 positions/vector
}

impl LsbLde64Tables {
    pub fn new(omega64: BabyBearField, gamma: BabyBearField) -> Self {
        assert!(omega64.pow(64).is_one());
        assert!(!omega64.pow(32).is_one());
        let lanes = |a: [BabyBearField; 4]| unsafe {
            let raw = [
                a[0].raw_u32_value(),
                a[1].raw_u32_value(),
                a[2].raw_u32_value(),
                a[3].raw_u32_value(),
            ];
            vld1q_u32(raw.as_ptr())
        };
        let one = BabyBearField::ONE;
        let wi = omega64.inverse().expect("invertible");
        let inv64 = BabyBearField::from_u32_with_reduction(64)
            .inverse()
            .expect("64 invertible");
        let mut scale = [BabyBearField::ZERO; 64];
        for m in 0..64 {
            let mut t = gamma.pow(m as u32);
            t.mul_assign(&inv64);
            scale[bitrev6(m)] = t;
        }
        let stage = |root: BabyBearField, e_step: u32, m: usize| -> [BabyBearField; 4] {
            core::array::from_fn(|lane| root.pow(e_step * (4 * m as u32 + lane as u32)))
        };
        LsbLde64Tables {
            inv_d32: core::array::from_fn(|m| lanes(stage(wi, 1, m))),
            inv_d16: core::array::from_fn(|m| lanes(stage(wi, 2, m))),
            inv_d8: core::array::from_fn(|m| lanes(stage(wi, 4, m))),
            inv_d4: lanes([one, wi.pow(8), wi.pow(16), wi.pow(24)]),
            inv_tw2: lanes([one, one, one, wi.pow(16)]),
            fwd_d32: core::array::from_fn(|m| lanes(stage(omega64, 1, m))),
            fwd_d16: core::array::from_fn(|m| lanes(stage(omega64, 2, m))),
            fwd_d8: core::array::from_fn(|m| lanes(stage(omega64, 4, m))),
            fwd_d4: lanes([one, omega64.pow(8), omega64.pow(16), omega64.pow(24)]),
            fwd_tw2: lanes([one, one, one, omega64.pow(16)]),
            scale: core::array::from_fn(|m| {
                lanes(core::array::from_fn(|lane| scale[4 * m + lane]))
            }),
        }
    }
}

/// LDE of one row's 64 contiguous cells (16 vectors, 4 cells each): values on
/// H64 (natural order) -> values on the coset gamma*H64 (natural order).
#[inline(always)]
pub unsafe fn lsb_lde64_base(h: &[uint32x4_t; 16], t: &LsbLde64Tables) -> [uint32x4_t; 16] {
    let mut x = *h;
    // ---- DIF inverse NTT ----
    for m in 0..8 {
        let a = x[m];
        let b = x[m + 8];
        x[m] = add4(a, b);
        x[m + 8] = mont_mul4(sub4(a, b), t.inv_d32[m]);
    }
    for blk in [0usize, 8] {
        for m in 0..4 {
            let a = x[blk + m];
            let b = x[blk + m + 4];
            x[blk + m] = add4(a, b);
            x[blk + m + 4] = mont_mul4(sub4(a, b), t.inv_d16[m]);
        }
    }
    for blk in [0usize, 4, 8, 12] {
        for m in 0..2 {
            let a = x[blk + m];
            let b = x[blk + m + 2];
            x[blk + m] = add4(a, b);
            x[blk + m + 2] = mont_mul4(sub4(a, b), t.inv_d8[m]);
        }
    }
    let mut blk = 0;
    while blk < 16 {
        let a = x[blk];
        let b = x[blk + 1];
        x[blk] = add4(a, b);
        x[blk + 1] = mont_mul4(sub4(a, b), t.inv_d4);
        blk += 2;
    }
    for m in 0..16 {
        x[m] = lsb_dif_tail(x[m], t.inv_tw2);
    }
    // ---- coset + 1/64 diagonal (bit-reversed positions) ----
    for m in 0..16 {
        x[m] = mont_mul4(x[m], t.scale[m]);
    }
    // ---- DIT forward NTT ----
    for m in 0..16 {
        x[m] = lsb_dit_head(x[m], t.fwd_tw2);
    }
    let mut blk = 0;
    while blk < 16 {
        let a = x[blk];
        let tt = mont_mul4(x[blk + 1], t.fwd_d4);
        x[blk] = add4(a, tt);
        x[blk + 1] = sub4(a, tt);
        blk += 2;
    }
    for blk in [0usize, 4, 8, 12] {
        for m in 0..2 {
            let a = x[blk + m];
            let tt = mont_mul4(x[blk + m + 2], t.fwd_d8[m]);
            x[blk + m] = add4(a, tt);
            x[blk + m + 2] = sub4(a, tt);
        }
    }
    for blk in [0usize, 8] {
        for m in 0..4 {
            let a = x[blk + m];
            let tt = mont_mul4(x[blk + m + 4], t.fwd_d16[m]);
            x[blk + m] = add4(a, tt);
            x[blk + m + 4] = sub4(a, tt);
        }
    }
    for m in 0..8 {
        let a = x[m];
        let tt = mont_mul4(x[m + 8], t.fwd_d32[m]);
        x[m] = add4(a, tt);
        x[m + 8] = sub4(a, tt);
    }
    x
}

// ---- generic AoS cell kernels for the LSB evaluators ----

/// `dst[i] += src[i]` over N contiguous base cells.
#[inline(always)]
pub unsafe fn form_add_cells<const N: usize>(dst: *mut BabyBearField, src: *const BabyBearField) {
    let dst = dst as *mut u32;
    let src = src as *const u32;
    let mut i = 0;
    while i + 4 <= N {
        vst1q_u32(
            dst.add(i),
            add4(vld1q_u32(dst.add(i)), vld1q_u32(src.add(i))),
        );
        i += 4;
    }
    while i < N {
        let mut a = *dst.add(i) + *src.add(i);
        if a >= P {
            a -= P;
        }
        *dst.add(i) = a;
        i += 1;
    }
}

/// `dst[i] -= src[i]` over N contiguous base cells.
#[inline(always)]
pub unsafe fn form_sub_cells<const N: usize>(dst: *mut BabyBearField, src: *const BabyBearField) {
    let dst = dst as *mut u32;
    let src = src as *const u32;
    let mut i = 0;
    while i + 4 <= N {
        vst1q_u32(
            dst.add(i),
            sub4(vld1q_u32(dst.add(i)), vld1q_u32(src.add(i))),
        );
        i += 4;
    }
    while i < N {
        let (a, b) = (*dst.add(i), *src.add(i));
        *dst.add(i) = if a >= b { a - b } else { a + P - b };
        i += 1;
    }
}

/// `dst[i] += c * src[i]` over N contiguous base cells.
#[inline(always)]
pub unsafe fn form_muladd_cells<const N: usize>(
    dst: *mut BabyBearField,
    src: *const BabyBearField,
    c: BabyBearField,
) {
    let cv = vdupq_n_u32(c.raw_u32_value());
    let dst = dst as *mut u32;
    let src = src as *const u32;
    let mut i = 0;
    while i + 4 <= N {
        vst1q_u32(
            dst.add(i),
            add4(
                vld1q_u32(dst.add(i)),
                mont_mul4(vld1q_u32(src.add(i)), cv),
            ),
        );
        i += 4;
    }
    while i < N {
        let mut t = [0u32; 4];
        vst1q_u32(
            t.as_mut_ptr(),
            mont_mul4(vdupq_n_u32(*src.add(i)), cv),
        );
        let mut a = *dst.add(i) + t[0];
        if a >= P {
            a -= P;
        }
        *dst.add(i) = a;
        i += 1;
    }
}

/// `dst[i] += coeff * a[i]` over ALL N cells (dense packed linear term).
#[inline(always)]
pub unsafe fn lin_base_cells_all<const N: usize>(
    dst: *mut BabyBearExt4,
    a: *const BabyBearField,
    coeff: &BabyBearExt4,
) {
    let cv = load_e(coeff);
    let a = a as *const u32;
    for i in 0..N {
        let d = dst.add(i);
        store_e(d, add4(load_e(d), mont_mul4(cv, vdupq_n_u32(*a.add(i)))));
    }
}

/// `dst[i] += coeff (x) a[i]` over ALL N cells.
#[inline(always)]
pub unsafe fn lin_ext_cells_all<const N: usize>(
    dst: *mut BabyBearExt4,
    a: *const BabyBearExt4,
    coeff: &BabyBearExt4,
) {
    let m = ExtMatrix::new(coeff);
    for i in 0..N {
        let d = dst.add(i);
        store_e(d, add4(load_e(d), mat_mul(&m, load_e(a.add(i)))));
    }
}

/// `dst[i] += c` over N cells.
#[inline(always)]
pub unsafe fn add_const_cells<const N: usize>(dst: *mut BabyBearExt4, c: &BabyBearExt4) {
    let cv = load_e(c);
    for i in 0..N {
        let d = dst.add(i);
        store_e(d, add4(load_e(d), cv));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ::field::{Field, FieldExtension};

    fn pseudo_base(seed: &mut u64) -> BabyBearField {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        BabyBearField::from_u32_with_reduction((*seed >> 33) as u32)
    }

    fn pseudo_ext(seed: &mut u64) -> BabyBearExt4 {
        BabyBearExt4::from_array_of_base(core::array::from_fn(|_| pseudo_base(seed)))
    }

    #[test]
    fn neon_ext_mul_matches_scalar() {
        let mut seed = 7u64;
        for _ in 0..1000 {
            let a = pseudo_ext(&mut seed);
            let b = pseudo_ext(&mut seed);
            let mut expected = a;
            expected.mul_assign(&b);

            let got: BabyBearExt4 = unsafe {
                let r11v = vdupq_n_u32(r11());
                core::mem::transmute(ext_mul_var(load_e(&a), load_e(&b), r11v))
            };
            assert_eq!(got, expected);

            let m = ExtMatrix::new(&b);
            let got2: BabyBearExt4 = unsafe { core::mem::transmute(mat_mul(&m, load_e(&a))) };
            assert_eq!(got2, expected);
        }
    }

    #[test]
    fn neon_lde8_matches_direct_evaluation() {
        use ::field::PrimeField;
        // omega16 for BabyBear via the fft crate's generator
        let omega16 = ::fft::domain_generator_for_size::<BabyBearField>(16);
        let mut omega8 = omega16;
        omega8.square();
        let tables = SoaLde8Tables::new(omega8, omega16);

        let mut seed = 33u64;
        for _ in 0..50 {
            // random degree-7 coefficients, one set per lane
            let coeffs: [[BabyBearField; 4]; 8] =
                core::array::from_fn(|_| core::array::from_fn(|_| pseudo_base(&mut seed)));
            // evaluate on H = <omega8> per lane, pack lanes
            let mut cells = [[0u32; 4]; 8];
            for j in 0..8 {
                let x = omega8.pow(j as u32);
                for lane in 0..4 {
                    let mut acc = BabyBearField::ZERO;
                    for i in (0..8).rev() {
                        acc.mul_assign(&x);
                        acc.add_assign(&coeffs[i][lane]);
                    }
                    cells[j][lane] = acc.raw_u32_value();
                }
            }
            let cells_v: [uint32x4_t; 8] =
                core::array::from_fn(|j| unsafe { vld1q_u32(cells[j].as_ptr()) });
            let out = unsafe { soa_lde8(&cells_v, &tables) };
            // direct evaluation at gamma * omega8^j
            for j in 0..8 {
                let mut x = omega16;
                x.mul_assign(&omega8.pow(j as u32));
                let mut got = [0u32; 4];
                unsafe { vst1q_u32(got.as_mut_ptr(), out[j]) };
                for lane in 0..4 {
                    let mut acc = BabyBearField::ZERO;
                    for i in (0..8).rev() {
                        acc.mul_assign(&x);
                        acc.add_assign(&coeffs[i][lane]);
                    }
                    assert_eq!(
                        got[lane],
                        acc.raw_u32_value(),
                        "lde8 mismatch at coset point {} lane {}",
                        j,
                        lane
                    );
                }
            }
        }
    }

    #[test]
    fn neon_lsb_lde_matches_direct_evaluation() {
        use ::field::PrimeField;
        let omega16 = ::fft::domain_generator_for_size::<BabyBearField>(16);
        let mut omega8 = omega16;
        omega8.square();
        let t8 = LsbLde8Tables::new(omega8, omega16);
        let t8m = LsbLde8MatTables::new(omega8, omega16);
        let omega128 = ::fft::domain_generator_for_size::<BabyBearField>(128);
        let mut omega64 = omega128;
        omega64.square();
        let t64 = LsbLde64Tables::new(omega64, omega128);

        let eval = |coeffs: &[BabyBearField], x: BabyBearField| -> BabyBearField {
            let mut acc = BabyBearField::ZERO;
            for c in coeffs.iter().rev() {
                acc.mul_assign(&x);
                acc.add_assign(c);
            }
            acc
        };

        let mut seed = 91u64;
        for _ in 0..50 {
            // n = 8: one row, cells are lanes
            let coeffs: [BabyBearField; 8] = core::array::from_fn(|_| pseudo_base(&mut seed));
            let mut cells = [0u32; 8];
            for j in 0..8 {
                cells[j] = eval(&coeffs, omega8.pow(j as u32)).raw_u32_value();
            }
            let out = unsafe {
                let h = [
                    vld1q_u32(cells.as_ptr()),
                    vld1q_u32(cells.as_ptr().add(4)),
                ];
                let o = lsb_lde8_base(h, &t8);
                // the partially-reduced variant canonicalizes its outputs, so
                // it must agree bitwise with the canonical kernel
                let o_lazy = lsb_lde8_base_lazy(h, &t8);
                let o_mat = lsb_lde8_base_mat(h, &t8m);
                let mut raw = [0u32; 8];
                let mut raw_lazy = [0u32; 8];
                let mut raw_mat = [0u32; 8];
                vst1q_u32(raw.as_mut_ptr(), o[0]);
                vst1q_u32(raw.as_mut_ptr().add(4), o[1]);
                vst1q_u32(raw_lazy.as_mut_ptr(), o_lazy[0]);
                vst1q_u32(raw_lazy.as_mut_ptr().add(4), o_lazy[1]);
                vst1q_u32(raw_mat.as_mut_ptr(), o_mat[0]);
                vst1q_u32(raw_mat.as_mut_ptr().add(4), o_mat[1]);
                assert_eq!(raw, raw_lazy, "lazy lde8 diverges from canonical");
                assert_eq!(raw, raw_mat, "matrix lde8 diverges from canonical");
                raw
            };
            for j in 0..8 {
                let mut x = omega16;
                x.mul_assign(&omega8.pow(j as u32));
                assert_eq!(
                    out[j],
                    eval(&coeffs, x).raw_u32_value(),
                    "lsb lde8 mismatch at coset point {}",
                    j
                );
            }

            // n = 64
            let coeffs: [BabyBearField; 64] = core::array::from_fn(|_| pseudo_base(&mut seed));
            let mut cells = [0u32; 64];
            for j in 0..64 {
                cells[j] = eval(&coeffs, omega64.pow(j as u32)).raw_u32_value();
            }
            let out = unsafe {
                let h: [uint32x4_t; 16] =
                    core::array::from_fn(|m| vld1q_u32(cells.as_ptr().add(4 * m)));
                let o = lsb_lde64_base(&h, &t64);
                let mut raw = [0u32; 64];
                for m in 0..16 {
                    vst1q_u32(raw.as_mut_ptr().add(4 * m), o[m]);
                }
                raw
            };
            for j in 0..64 {
                let mut x = omega128;
                x.mul_assign(&omega64.pow(j as u32));
                assert_eq!(
                    out[j],
                    eval(&coeffs, x).raw_u32_value(),
                    "lsb lde64 mismatch at coset point {}",
                    j
                );
            }
        }
    }

    #[test]
    fn neon_lde64_variants_match_direct_evaluation() {
        use ::field::PrimeField;
        let omega128 = ::fft::domain_generator_for_size::<BabyBearField>(128);
        let mut omega64 = omega128;
        omega64.square();
        let tables = SoaLde64Tables::new(omega64, omega128);

        let mut seed = 77u64;
        for _ in 0..5 {
            let coeffs: [[BabyBearField; 4]; 64] =
                core::array::from_fn(|_| core::array::from_fn(|_| pseudo_base(&mut seed)));
            let mut cells = [[0u32; 4]; 64];
            for j in 0..64 {
                let x = omega64.pow(j as u32);
                for lane in 0..4 {
                    let mut acc = BabyBearField::ZERO;
                    for i in (0..64).rev() {
                        acc.mul_assign(&x);
                        acc.add_assign(&coeffs[i][lane]);
                    }
                    cells[j][lane] = acc.raw_u32_value();
                }
            }
            let cells_v: [uint32x4_t; 64] =
                core::array::from_fn(|j| unsafe { vld1q_u32(cells[j].as_ptr()) });
            let out_r2 = unsafe { soa_lde64_r2(&cells_v, &tables) };
            let out_r8 = unsafe { soa_lde64_r8(&cells_v, &tables) };
            for j in 0..64 {
                let mut x = omega128;
                x.mul_assign(&omega64.pow(j as u32));
                let mut got2 = [0u32; 4];
                let mut got8 = [0u32; 4];
                unsafe {
                    vst1q_u32(got2.as_mut_ptr(), out_r2[j]);
                    vst1q_u32(got8.as_mut_ptr(), out_r8[j]);
                }
                for lane in 0..4 {
                    let mut acc = BabyBearField::ZERO;
                    for i in (0..64).rev() {
                        acc.mul_assign(&x);
                        acc.add_assign(&coeffs[i][lane]);
                    }
                    assert_eq!(got2[lane], acc.raw_u32_value(), "r2 mismatch at {}", j);
                    assert_eq!(got8[lane], acc.raw_u32_value(), "r8 mismatch at {}", j);
                }
            }
        }
    }

    #[test]
    fn neon_lazy_accumulation_matches_reduced() {
        let mut seed = 21u64;
        // enough terms to cross several cond-sub boundaries
        for _ in 0..20 {
            let terms: Vec<([BabyBearField; 27], [BabyBearField; 27], BabyBearExt4)> = (0..7)
                .map(|_| {
                    (
                        core::array::from_fn(|_| pseudo_base(&mut seed)),
                        core::array::from_fn(|_| pseudo_base(&mut seed)),
                        pseudo_ext(&mut seed),
                    )
                })
                .collect();
            let lin: ([BabyBearField; 27], BabyBearExt4) = (
                core::array::from_fn(|_| pseudo_base(&mut seed)),
                pseudo_ext(&mut seed),
            );

            // reduced reference
            let mut expected = [BabyBearExt4::ZERO; 27];
            unsafe {
                for (a, b, c) in terms.iter() {
                    quad_base_cells::<27>(expected.as_mut_ptr(), a.as_ptr(), b.as_ptr(), c);
                }
                linear_base_27(expected.as_mut_ptr(), lin.0.as_ptr(), &lin.1);
            }

            // lazy path with the static cond-sub cadence
            let mut acc = [0u64; 27 * 4];
            let mut out = [BabyBearExt4::ZERO; 27];
            unsafe {
                let mut count = 0;
                for (a, b, c) in terms.iter() {
                    lazy_quad_base_cells::<27>(acc.as_mut_ptr(), a.as_ptr(), b.as_ptr(), c);
                    count += 1;
                    if count == 2 {
                        lazy_condsub_cells::<27>(acc.as_mut_ptr());
                        count = 0;
                    }
                }
                lazy_linear_base_27(acc.as_mut_ptr(), lin.0.as_ptr(), &lin.1);
                lazy_finalize_cells::<27>(acc.as_mut_ptr(), out.as_mut_ptr());
            }
            assert_eq!(out, expected);
            assert!(acc.iter().all(|el| *el == 0), "finalize must zero the acc");
        }
    }

    #[test]
    fn neon_folds_match_scalar() {
        let mut seed = 11u64;
        let base: Vec<BabyBearField> = (0..64).map(|_| pseudo_base(&mut seed)).collect();
        let ext: Vec<BabyBearExt4> = (0..64).map(|_| pseudo_ext(&mut seed)).collect();
        let prefix: [BabyBearExt4; 8] = core::array::from_fn(|_| pseudo_ext(&mut seed));
        let prefix4: [BabyBearExt4; 4] = core::array::from_fn(|_| pseudo_ext(&mut seed));
        let ch = pseudo_ext(&mut seed);

        for row in 0..8 {
            let stride = 8;
            // scalar references
            let mut expected_b = BabyBearExt4::ZERO;
            let mut expected_e = BabyBearExt4::ZERO;
            for i in 0..8 {
                let mut t = prefix[i];
                t.mul_assign_by_base(&base[row + i * stride]);
                expected_b.add_assign(&t);
                let mut t = prefix[i];
                t.mul_assign(&ext[row + i * stride]);
                expected_e.add_assign(&t);
            }
            let got_b = unsafe { fold8_base(base.as_ptr(), &prefix, stride, row) };
            let got_e = unsafe { fold8_ext(ext.as_ptr(), &prefix, stride, row) };
            assert_eq!(got_b, expected_b);
            assert_eq!(got_e, expected_e);

            // fused-pair variants must agree with two single folds
            let row1 = (row + 3) % 8;
            let (p0, p1) = unsafe { fold8_base_x2(base.as_ptr(), &prefix, stride, row, row1) };
            assert_eq!(p0, expected_b);
            assert_eq!(p1, unsafe {
                fold8_base(base.as_ptr(), &prefix, stride, row1)
            });
            let (q0, q1) = unsafe { fold8_ext_x2(ext.as_ptr(), &prefix, stride, row, row1) };
            assert_eq!(q0, expected_e);
            assert_eq!(q1, unsafe {
                fold8_ext(ext.as_ptr(), &prefix, stride, row1)
            });

            let mut expected_4 = BabyBearExt4::ZERO;
            for i in 0..4 {
                let mut t = prefix4[i];
                t.mul_assign(&ext[row + i * stride]);
                expected_4.add_assign(&t);
            }
            let got_4 = unsafe { fold4_ext(ext.as_ptr(), &prefix4, stride, row) };
            assert_eq!(got_4, expected_4);

            let mut expected_2 = ext[row + stride];
            expected_2.sub_assign(&ext[row]);
            expected_2.mul_assign(&ch);
            expected_2.add_assign(&ext[row]);
            let got_2 = unsafe { fold2_ext(ext.as_ptr(), &ch, stride, row) };
            assert_eq!(got_2, expected_2);
        }
    }
}
