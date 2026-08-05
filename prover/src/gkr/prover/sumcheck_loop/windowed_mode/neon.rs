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
unsafe fn mont_mul4(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
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
unsafe fn add4(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    let sum = vaddq_u32(a, b);
    vminq_u32(sum, vsubq_u32(sum, vdupq_n_u32(P)))
}

#[inline(always)]
unsafe fn sub4(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
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
fn r11() -> u32 {
    BabyBearField::new(11).raw_u32_value()
}

/// `a (x) b` for two variable `Ext4` values: build the permuted/scaled columns
/// of `b` (1 mult + 3 shuffles), then accumulate the lane-broadcast products.
#[inline(always)]
unsafe fn ext_mul_var(a: uint32x4_t, b: uint32x4_t, r11v: uint32x4_t) -> uint32x4_t {
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
unsafe fn mat_mul(m: &ExtMatrix, a: uint32x4_t) -> uint32x4_t {
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
pub unsafe fn soa_quad_bb_lazy(
    acc: *mut u64, // [27][4 limbs][4 rows]
    a: *const u32,
    b: *const u32,
    coeff: &BabyBearExt4,
) {
    let climbs: [u32; 4] = core::mem::transmute(*coeff);
    for c in 0..27 {
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
pub unsafe fn soa_lazy_condsub(acc: *mut u64) {
    let rp = vdupq_n_u64(RP);
    for i in 0..(27 * 8) {
        let p = acc.add(2 * i);
        let x = vld1q_u64(p);
        let mask = vcgeq_u64(x, rp);
        vst1q_u64(p, vsubq_u64(x, vandq_u64(mask, rp)));
    }
}

/// Final REDC + canonicalization of the SoA lazy accumulator into canonical
/// SoA u32 cells; zeroes the accumulator.
#[inline(always)]
pub unsafe fn soa_lazy_finalize(acc: *mut u64, out: *mut u32) {
    let rp = vdupq_n_u64(RP);
    let p2 = vdup_n_u32(P);
    let k2 = vdup_n_u32(K);
    let pq = vdupq_n_u32(P);
    for i in 0..(27 * 4) {
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
pub unsafe fn soa_quad_be(
    dst: *mut u32,
    a_ext: *const u32,
    b_base: *const u32,
    coeff_bcast: &[uint32x4_t; 4],
    r11v: uint32x4_t,
) {
    for c in 0..27 {
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
pub unsafe fn soa_apply_eq_and_accumulate(
    acc: *mut u32,
    lazy_out: *const u32,
    reduced: *mut u32,
    eq_soa: &[uint32x4_t; 4],
    r11v: uint32x4_t,
) {
    for c in 0..27 {
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
