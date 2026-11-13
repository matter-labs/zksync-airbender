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
// Lazy u64 accumulation bound (P = BabyBear, R = 2^32): each accumulated lane
// product is `coeff_j * t` with both factors canonical (< P), so < P^2 ~ 2^61.82.
// REDC needs its input below R*P ~ 2^62.91 to give a < 2P output, hence the
// static cadence: after every 2 accumulated products one conditional
// subtraction of R*P (a multiple of P, so a no-op mod P) restores the invariant
// `X < R*P` (X < R*P + 2*P^2 < 2^64 never overflows, and X - R*P < 2*P^2 < R*P).
// ---------------------------------------------------------------------------

const RP: u64 = (P as u64) << 32;

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

/// LSB-layout 8-tap fold of a base poly, 4 consecutive OUTPUT rows per call:
/// the rows' 32 contiguous taps are transposed in-register (2 x 4x4) into
/// tap-column vectors (lanes = rows), then lazy-accumulated against the
/// broadcast ext weights. Returns the limb-major SoA block of the 4 folded
/// ext values.
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
/// tap's canonical [`SoaExtTable`].
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

/// `dst[cell] += src[cell]` over N ext SoA cells (form build, folded stages).
#[inline(always)]
pub unsafe fn soa_ext_form_add_n<const N: usize>(dst: *mut u32, src: *const u32) {
    for i in 0..(4 * N) {
        let p = dst.add(4 * i);
        vst1q_u32(p, add4(vld1q_u32(p), vld1q_u32(src.add(4 * i))));
    }
}

/// `dst[cell] = src[cell]` over N ext SoA cells — the FIRST form member's
/// pure store (the destination is never pre-zeroed).
#[inline(always)]
pub unsafe fn soa_ext_form_store_n<const N: usize>(dst: *mut u32, src: *const u32) {
    for i in 0..(4 * N) {
        vst1q_u32(dst.add(4 * i), vld1q_u32(src.add(4 * i)));
    }
}

/// `dst[cell] = -src[cell]` over N ext SoA cells (first-member store form of
/// [`soa_ext_form_sub_n`]; identical values to `0 - src`).
#[inline(always)]
pub unsafe fn soa_ext_form_neg_store_n<const N: usize>(dst: *mut u32, src: *const u32) {
    let zero = vdupq_n_u32(0);
    for i in 0..(4 * N) {
        vst1q_u32(dst.add(4 * i), sub4(zero, vld1q_u32(src.add(4 * i))));
    }
}

/// `dst[cell] = c * src[cell]` over N ext SoA cells (first-member store form
/// of [`soa_ext_form_muladd_n`]; identical values to `0 + c*src`).
#[inline(always)]
pub unsafe fn soa_ext_form_mul_store_n<const N: usize>(
    dst: *mut u32,
    src: *const u32,
    c: BabyBearField,
) {
    let cv = vdupq_n_u32(c.raw_u32_value());
    for i in 0..(4 * N) {
        vst1q_u32(dst.add(4 * i), mont_mul4(vld1q_u32(src.add(4 * i)), cv));
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

/// `dst[cell] = src[cell]` over N base SoA cells — the FIRST form member's
/// pure store (the destination is never pre-zeroed).
#[inline(always)]
pub unsafe fn soa_base_form_store_n<const N: usize>(dst: *mut u32, src: *const u32) {
    for i in 0..N {
        vst1q_u32(dst.add(4 * i), vld1q_u32(src.add(4 * i)));
    }
}

/// `dst[cell] = -src[cell]` (first-member store form of
/// [`soa_base_form_sub_n`]; identical values to `0 - src`).
#[inline(always)]
pub unsafe fn soa_base_form_neg_store_n<const N: usize>(dst: *mut u32, src: *const u32) {
    let zero = vdupq_n_u32(0);
    for i in 0..N {
        vst1q_u32(dst.add(4 * i), sub4(zero, vld1q_u32(src.add(4 * i))));
    }
}

/// `dst[cell] = c * src[cell]` (first-member store form of
/// [`soa_base_form_muladd_n`]; identical values to `0 + c*src`).
#[inline(always)]
pub unsafe fn soa_base_form_mul_store_n<const N: usize>(
    dst: *mut u32,
    src: *const u32,
    c: BabyBearField,
) {
    let cv = vdupq_n_u32(c.raw_u32_value());
    for i in 0..N {
        vst1q_u32(dst.add(4 * i), mont_mul4(vld1q_u32(src.add(4 * i)), cv));
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

/// `dst[cell] += c` over the FIRST N base SoA cell groups -- a mixed-degree
/// form's constant, applied to real evaluation cells only (a constant has no
/// leading coefficient, so difference/infinity cells never see it).
#[inline(always)]
pub unsafe fn soa_base_form_add_const_n<const N: usize>(dst: *mut u32, c: BabyBearField) {
    let cv = vdupq_n_u32(c.raw_u32_value());
    for i in 0..N {
        let p = dst.add(4 * i);
        vst1q_u32(p, add4(vld1q_u32(p), cv));
    }
}

/// Ext twin of [`soa_base_form_add_const_n`]: the base constant lands on
/// limb 0 only (`add_assign_base`), over the FIRST N ext SoA cell groups.
#[inline(always)]
pub unsafe fn soa_ext_form_add_base_const_n<const N: usize>(dst: *mut u32, c: BabyBearField) {
    let cv = vdupq_n_u32(c.raw_u32_value());
    for g in 0..N {
        let p = dst.add(16 * g);
        vst1q_u32(p, add4(vld1q_u32(p), cv));
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
// and one call processes ONE row -- 4 CELLS per vector for base values, one
// ext element per vector. The NEON GKR backend uses these through the
// `lsb_bench` LSB same-size chain.
// ---------------------------------------------------------------------------

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

#[cfg(test)]
mod tests {
    use super::*;
    use ::field::Field;

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
    fn neon_lsb_lde_matches_direct_evaluation() {
        let omega16 = ::fft::domain_generator_for_size::<BabyBearField>(16);
        let mut omega8 = omega16;
        omega8.square();
        let t8m = LsbLde8MatTables::new(omega8, omega16);

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
            let coeffs: [BabyBearField; 8] = core::array::from_fn(|_| pseudo_base(&mut seed));
            let mut cells = [0u32; 8];
            for j in 0..8 {
                cells[j] = eval(&coeffs, omega8.pow(j as u32)).raw_u32_value();
            }
            let out = unsafe {
                let h = [vld1q_u32(cells.as_ptr()), vld1q_u32(cells.as_ptr().add(4))];
                let o = lsb_lde8_base_mat(h, &t8m);
                let mut raw = [0u32; 8];
                vst1q_u32(raw.as_mut_ptr(), o[0]);
                vst1q_u32(raw.as_mut_ptr().add(4), o[1]);
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
        }
    }
}
