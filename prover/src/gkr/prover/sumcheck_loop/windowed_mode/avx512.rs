//! x86-64 AVX-512 primitives for the window-3 SoA sumcheck kernels — the
//! 16-lane twin of [`super::avx2`], specialized for `BabyBearField` /
//! `BabyBearExt4` (Montgomery form, `Ext4` = 4 contiguous Montgomery `u32`
//! limbs).
//!
//! Lane conventions (see [`super::lsb_avx512`] for the grid layout): a SoA
//! cell group holds 16 consecutive CELLS of one row per vector, one vector
//! per limb; the 27-cell `{0,1,inf}^3` window grid is exactly TWO groups
//! (cells 0..16 and 16..32, the last five padding). The lazy u64
//! accumulators keep the products of the even and odd cells in two vectors
//! (the natural `vpmuludq` output) and merge them back at REDC time. The
//! arithmetic is lane-for-lane the AVX2 one (canonical Montgomery products,
//! the flat quartic `Ext4` table with `alpha^2 = 11`, `beta^2 = alpha`,
//! raw `< P^2` lazy products kept `< R*P` by a conditional `R*P`
//! subtraction after every two products), so every result is byte-identical
//! to the scalar and AVX2 kernels.
//!
//! Every function carries `#[target_feature(enable = "avx512f")]` so the
//! enclosing crate keeps plain AVX2 code generation; the backend checks
//! `is_x86_feature_detected!("avx512f")` before selecting these kernels.
#![allow(clippy::missing_safety_doc)]

use core::arch::x86_64::*;

use ::field::baby_bear::base::BabyBearField;
use ::field::baby_bear::ext4::BabyBearExt4;
use ::field::{Field, PrimeField};

pub(crate) const P: u32 = 0x78000001;
pub(crate) const K: u32 = 0x77ffffff; // -P^{-1} mod 2^32
const RP: u64 = (P as u64) << 32;

#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn pv() -> __m512i {
    _mm512_set1_epi32(P as i32)
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn kv() -> __m512i {
    _mm512_set1_epi32(K as i32)
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn rpv() -> __m512i {
    _mm512_set1_epi64(RP as i64)
}
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn ld(p: *const u32) -> __m512i {
    _mm512_loadu_si512(p as *const __m512i)
}
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn st(p: *mut u32, v: __m512i) {
    _mm512_storeu_si512(p as *mut __m512i, v)
}
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn bc32(x: u32) -> __m512i {
    _mm512_set1_epi32(x as i32)
}
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn zero() -> __m512i {
    _mm512_setzero_si512()
}
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn idx(v: &[i32; 16]) -> __m512i {
    _mm512_loadu_si512(v.as_ptr() as *const __m512i)
}

/// Canonical Montgomery product on 16 lanes.
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn mont_mul16(a: __m512i, b: __m512i) -> __m512i {
    let lo = _mm512_mullo_epi32(a, b);
    let m = _mm512_mullo_epi32(lo, kv());
    let prod_e = _mm512_mul_epu32(a, b);
    let prod_o = _mm512_mul_epu32(_mm512_srli_epi64::<32>(a), _mm512_srli_epi64::<32>(b));
    let mp_e = _mm512_mul_epu32(m, pv());
    let mp_o = _mm512_mul_epu32(_mm512_srli_epi64::<32>(m), pv());
    let t_e = _mm512_add_epi64(prod_e, mp_e);
    let t_o = _mm512_add_epi64(prod_o, mp_o);
    let r = _mm512_mask_blend_epi32(0xAAAA, _mm512_srli_epi64::<32>(t_e), t_o);
    _mm512_min_epu32(r, _mm512_sub_epi32(r, pv()))
}
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn add16(a: __m512i, b: __m512i) -> __m512i {
    let s = _mm512_add_epi32(a, b);
    _mm512_min_epu32(s, _mm512_sub_epi32(s, pv()))
}
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn sub16(a: __m512i, b: __m512i) -> __m512i {
    let d = _mm512_sub_epi32(a, b);
    _mm512_min_epu32(d, _mm512_add_epi32(d, pv()))
}

/// Montgomery form of 11 (the quadratic non-residue of the tower), broadcast.
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn r11v() -> __m512i {
    bc32(BabyBearField::new(11).raw_u32_value())
}

/// Broadcast the limbs of one ext value to cell vectors.
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn bcast_ext(v: &BabyBearExt4) -> [__m512i; 4] {
    let limbs: [u32; 4] = core::mem::transmute(*v);
    [
        bc32(limbs[0]),
        bc32(limbs[1]),
        bc32(limbs[2]),
        bc32(limbs[3]),
    ]
}

/// Cell-pointwise `Ext4` multiplication in SoA form (flat quartic table).
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn soa_ext_mul(a: &[__m512i; 4], b: &[__m512i; 4], r11: __m512i) -> [__m512i; 4] {
    let p00 = mont_mul16(a[0], b[0]);
    let p01 = mont_mul16(a[0], b[1]);
    let p02 = mont_mul16(a[0], b[2]);
    let p03 = mont_mul16(a[0], b[3]);
    let p10 = mont_mul16(a[1], b[0]);
    let p11 = mont_mul16(a[1], b[1]);
    let p12 = mont_mul16(a[1], b[2]);
    let p13 = mont_mul16(a[1], b[3]);
    let p20 = mont_mul16(a[2], b[0]);
    let p21 = mont_mul16(a[2], b[1]);
    let p22 = mont_mul16(a[2], b[2]);
    let p23 = mont_mul16(a[2], b[3]);
    let p30 = mont_mul16(a[3], b[0]);
    let p31 = mont_mul16(a[3], b[1]);
    let p32 = mont_mul16(a[3], b[2]);
    let p33 = mont_mul16(a[3], b[3]);
    let out0 = add16(p00, mont_mul16(add16(add16(p11, p23), p32), r11));
    let out1 = add16(add16(p01, p10), add16(p22, mont_mul16(p33, r11)));
    let out2 = add16(add16(p02, p20), mont_mul16(add16(p13, p31), r11));
    let out3 = add16(add16(p03, p12), add16(p21, p30));
    [out0, out1, out2, out3]
}

/// LAZY cell-pointwise `Ext4` multiplication: `b`'s limbs 1..3 are
/// pre-scaled by 11 (three canonical products), then every output limb is
/// the u64 sum of its four raw cross products (`< 4 P^2`, no intermediate
/// reduction) and gets ONE REDC. Same values as [`soa_ext_mul`] with 7
/// canonical multiplies instead of 19.
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn soa_ext_mul_lazy(
    a: &[__m512i; 4],
    b: &[__m512i; 4],
    r11: __m512i,
) -> [__m512i; 4] {
    let b1s = mont_mul16(b[1], r11);
    let b2s = mont_mul16(b[2], r11);
    let b3s = mont_mul16(b[3], r11);
    let ah: [__m512i; 4] = core::array::from_fn(|i| hi64(a[i]));
    let bh: [__m512i; 4] = core::array::from_fn(|i| hi64(b[i]));
    let (b1sh, b2sh, b3sh) = (hi64(b1s), hi64(b2s), hi64(b3s));
    // out0 = a0 b0 + 11 a1 b1 + 11 a2 b3 + 11 a3 b2
    let mut l0 = Lazy16::zero();
    l0.mla_raw(a[0], ah[0], b[0], bh[0]);
    l0.mla_raw(a[1], ah[1], b1s, b1sh);
    l0.mla_raw(a[2], ah[2], b3s, b3sh);
    l0.mla_raw(a[3], ah[3], b2s, b2sh);
    // out1 = a0 b1 + a1 b0 + a2 b2 + 11 a3 b3
    let mut l1 = Lazy16::zero();
    l1.mla_raw(a[0], ah[0], b[1], bh[1]);
    l1.mla_raw(a[1], ah[1], b[0], bh[0]);
    l1.mla_raw(a[2], ah[2], b[2], bh[2]);
    l1.mla_raw(a[3], ah[3], b3s, b3sh);
    // out2 = a0 b2 + a2 b0 + 11 a1 b3 + 11 a3 b1
    let mut l2 = Lazy16::zero();
    l2.mla_raw(a[0], ah[0], b[2], bh[2]);
    l2.mla_raw(a[2], ah[2], b[0], bh[0]);
    l2.mla_raw(a[1], ah[1], b3s, b3sh);
    l2.mla_raw(a[3], ah[3], b1s, b1sh);
    // out3 = a0 b3 + a1 b2 + a2 b1 + a3 b0
    let mut l3 = Lazy16::zero();
    l3.mla_raw(a[0], ah[0], b[3], bh[3]);
    l3.mla_raw(a[1], ah[1], b[2], bh[2]);
    l3.mla_raw(a[2], ah[2], b[1], bh[1]);
    l3.mla_raw(a[3], ah[3], b[0], bh[0]);
    [l0.redc(), l1.redc(), l2.redc(), l3.redc()]
}

// ---------------------------------------------------------------------------
// lazy u64 accumulation (16 cells per limb: even-cell and odd-cell products)
// ---------------------------------------------------------------------------

/// One limb's lazy accumulator over 16 cells: raw `< R*P + 2 P^2` sums of
/// `coeff * value` products, even cells in `e`, odd cells in `o`.
#[derive(Clone, Copy)]
pub(crate) struct Lazy16 {
    pub(crate) e: __m512i,
    pub(crate) o: __m512i,
}

impl Lazy16 {
    #[inline]
    #[target_feature(enable = "avx512f")]
    pub(crate) unsafe fn zero() -> Self {
        Lazy16 {
            e: _mm512_setzero_si512(),
            o: _mm512_setzero_si512(),
        }
    }
    #[inline]
    #[target_feature(enable = "avx512f")]
    pub(crate) unsafe fn load(p: *const u64) -> Self {
        Lazy16 {
            e: _mm512_loadu_si512(p as *const __m512i),
            o: _mm512_loadu_si512(p.add(8) as *const __m512i),
        }
    }
    #[inline]
    #[target_feature(enable = "avx512f")]
    pub(crate) unsafe fn store(&self, p: *mut u64) {
        _mm512_storeu_si512(p as *mut __m512i, self.e);
        _mm512_storeu_si512(p.add(8) as *mut __m512i, self.o);
    }
    /// `+= coeff * v` lane-wise for a BROADCAST coefficient (`v_hi` is
    /// `v >> 32` per 64-bit lane, shared across the limbs of one product).
    #[inline]
    #[target_feature(enable = "avx512f")]
    pub(crate) unsafe fn mla(&mut self, coeff: __m512i, v: __m512i, v_hi: __m512i) {
        self.e = _mm512_add_epi64(self.e, _mm512_mul_epu32(coeff, v));
        self.o = _mm512_add_epi64(self.o, _mm512_mul_epu32(coeff, v_hi));
    }
    /// `+= x * y` lane-wise for two VARIABLE canonical vectors (`x_hi`,
    /// `y_hi` their odd-lane halves).
    #[inline]
    #[target_feature(enable = "avx512f")]
    pub(crate) unsafe fn mla_raw(&mut self, x: __m512i, x_hi: __m512i, y: __m512i, y_hi: __m512i) {
        self.e = _mm512_add_epi64(self.e, _mm512_mul_epu32(x, y));
        self.o = _mm512_add_epi64(self.o, _mm512_mul_epu32(x_hi, y_hi));
    }
    #[inline]
    #[target_feature(enable = "avx512f")]
    unsafe fn condsub_one(x: __m512i) -> __m512i {
        let m = _mm512_cmpge_epu64_mask(x, rpv());
        _mm512_mask_sub_epi64(x, m, x, rpv())
    }
    #[inline]
    #[target_feature(enable = "avx512f")]
    pub(crate) unsafe fn condsub(&mut self) {
        self.e = Self::condsub_one(self.e);
        self.o = Self::condsub_one(self.o);
    }
    /// One conditional `R*P` subtraction, REDC and canonicalization.
    #[inline]
    #[target_feature(enable = "avx512f")]
    pub(crate) unsafe fn redc(mut self) -> __m512i {
        self.condsub();
        let m_e = _mm512_mullo_epi32(self.e, kv());
        let m_o = _mm512_mullo_epi32(self.o, kv());
        let s_e = _mm512_add_epi64(self.e, _mm512_mul_epu32(m_e, pv()));
        let s_o = _mm512_add_epi64(self.o, _mm512_mul_epu32(m_o, pv()));
        let r = _mm512_mask_blend_epi32(0xAAAA, _mm512_srli_epi64::<32>(s_e), s_o);
        _mm512_min_epu32(r, _mm512_sub_epi32(r, pv()))
    }
}

#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn hi64(v: __m512i) -> __m512i {
    _mm512_srli_epi64::<32>(v)
}

/// Per-tap multiplication table of a fixed ext multiplier `p`, broadcast to
/// cell vectors: `(p (x) v)_j = sum_k m[j][k] * v_k` with canonical entries
/// (the `11*p_i` entries REDC'd once at build time), lazy-accumulable.
#[derive(Clone, Copy)]
pub(crate) struct ExtTable16 {
    pub(crate) m: [[__m512i; 4]; 4],
}

impl ExtTable16 {
    #[inline]
    #[target_feature(enable = "avx512f")]
    pub(crate) unsafe fn new(p: &BabyBearExt4) -> Self {
        let rows = table_rows(p);
        ExtTable16 {
            m: [
                [
                    bc32(rows[0][0]),
                    bc32(rows[0][1]),
                    bc32(rows[0][2]),
                    bc32(rows[0][3]),
                ],
                [
                    bc32(rows[1][0]),
                    bc32(rows[1][1]),
                    bc32(rows[1][2]),
                    bc32(rows[1][3]),
                ],
                [
                    bc32(rows[2][0]),
                    bc32(rows[2][1]),
                    bc32(rows[2][2]),
                    bc32(rows[2][3]),
                ],
                [
                    bc32(rows[3][0]),
                    bc32(rows[3][1]),
                    bc32(rows[3][2]),
                    bc32(rows[3][3]),
                ],
            ],
        }
    }
    /// `p (x) v` canonical: every output limb is the u64 sum of its four
    /// raw products (`< 4 P^2`) and gets one REDC.
    #[inline]
    #[target_feature(enable = "avx512f")]
    pub(crate) unsafe fn mul(&self, v: &[__m512i; 4], vh: &[__m512i; 4]) -> [__m512i; 4] {
        core::array::from_fn(|j| {
            let mut l = Lazy16::zero();
            l.mla(self.m[j][0], v[0], vh[0]);
            l.mla(self.m[j][1], v[1], vh[1]);
            l.mla(self.m[j][2], v[2], vh[2]);
            l.mla(self.m[j][3], v[3], vh[3]);
            l.redc()
        })
    }
    /// `acc[j] += sum_k m[j][k] * v[k]` with the lazy cadence (condsub after
    /// every two products).
    #[inline]
    #[target_feature(enable = "avx512f")]
    pub(crate) unsafe fn mla_into(
        &self,
        acc: &mut [Lazy16; 4],
        v: &[__m512i; 4],
        vh: &[__m512i; 4],
    ) {
        for j in 0..4 {
            acc[j].mla(self.m[j][0], v[0], vh[0]);
            acc[j].mla(self.m[j][1], v[1], vh[1]);
            acc[j].condsub();
            acc[j].mla(self.m[j][2], v[2], vh[2]);
            acc[j].mla(self.m[j][3], v[3], vh[3]);
            acc[j].condsub();
        }
    }
}

/// The canonical scalar rows of the ext multiplication table of `p`.
pub(crate) fn table_rows(p: &BabyBearExt4) -> [[u32; 4]; 4] {
    let l: [u32; 4] = unsafe { core::mem::transmute(*p) };
    let e11 = BabyBearField::new(11);
    let scaled: [u32; 4] = core::array::from_fn(|i| {
        let mut t = BabyBearField::from_raw_u32(l[i]);
        t.mul_assign(&e11);
        t.raw_u32_value()
    });
    [
        [l[0], scaled[1], scaled[3], scaled[2]],
        [l[1], l[0], l[2], scaled[3]],
        [l[2], scaled[3], l[0], scaled[1]],
        [l[3], l[2], l[1], l[0]],
    ]
}

// ---------------------------------------------------------------------------
// window-3 difference extrapolation in registers
// ---------------------------------------------------------------------------

/// Permutation tables of the in-register `{0,1,inf}^3` extrapolation: from
/// the 8 binary taps (lanes 0..8 of `b` for an even row, 8..16 for the odd
/// row sharing the same 16-tap load) to the two 16-cell groups of the SoA
/// grid, following the `W3_INF` dependency order (12 one-infinity cells from
/// the taps, 6 two-infinity cells from those, the all-infinity cell last).
#[derive(Clone, Copy)]
pub(crate) struct W3Perm {
    hi1: __m512i,
    lo1: __m512i,
    hi2: __m512i,
    lo2: __m512i,
    hi3: __m512i,
    lo3: __m512i,
    g0: __m512i,
    g0t2: __m512i,
    g1: __m512i,
    /// non-interpolated slots: the taps into cells 0..8, the rest zero
    plain: __m512i,
}

impl W3Perm {
    #[target_feature(enable = "avx512f")]
    pub(crate) unsafe fn new(odd: bool) -> Self {
        let o = if odd { 8 } else { 0 };
        // t1 lanes: c8 c9 c10 c11 c12 c13 c15 c16 c18 c19 c21 c22
        let hi1 = [1, 3, 5, 7, 2, 3, 6, 7, 4, 5, 6, 7, 0, 0, 0, 0].map(|x| x + o);
        let lo1 = [0, 2, 4, 6, 0, 1, 4, 5, 0, 1, 2, 3, 0, 0, 0, 0].map(|x| x + o);
        // t2 lanes: c14=(t1[1],t1[0]) c17=(3,2) c20=(2,0) c23=(3,1) c24=(6,4) c25=(7,5)
        let hi2 = [1, 3, 2, 3, 6, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        let lo2 = [0, 2, 0, 1, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
        // t3 lane 10: c26 = c17 - c14 = t2[1] - t2[0]
        let mut hi3 = [0i32; 16];
        hi3[10] = 1;
        let lo3 = [0i32; 16];
        // g0: lanes 0..8 taps, 8..14 = t1[0..6], 14 placeholder, 15 = t1[6]
        let g0: [i32; 16] = core::array::from_fn(|l| {
            if l < 8 {
                l as i32 + o
            } else if l < 14 {
                16 + (l as i32 - 8)
            } else if l == 14 {
                16
            } else {
                16 + 6
            }
        });
        let g0t2 = [0i32; 16];
        // g1 (over t1 | t2): c16=t1[7] c17=t2[1] c18=t1[8] c19=t1[9] c20=t2[2]
        // c21=t1[10] c22=t1[11] c23=t2[3] c24=t2[4] c25=t2[5] c26 placeholder
        let g1 = [7, 17, 8, 9, 18, 10, 11, 19, 20, 21, 0, 0, 0, 0, 0, 0];
        let plain: [i32; 16] = core::array::from_fn(|l| if l < 8 { l as i32 + o } else { 0 });
        Self {
            hi1: idx(&hi1),
            lo1: idx(&lo1),
            hi2: idx(&hi2),
            lo2: idx(&lo2),
            hi3: idx(&hi3),
            lo3: idx(&lo3),
            g0: idx(&g0),
            g0t2: idx(&g0t2),
            g1: idx(&g1),
            plain: idx(&plain),
        }
    }
}

/// The two 16-cell groups of an interpolated slot's window grid from its
/// taps (canonical lanes in, canonical lanes out; padding cells zero).
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn extrapolate(b: __m512i, p: &W3Perm) -> (__m512i, __m512i) {
    let t1 = sub16(
        _mm512_permutexvar_epi32(p.hi1, b),
        _mm512_permutexvar_epi32(p.lo1, b),
    );
    let t2 = sub16(
        _mm512_permutexvar_epi32(p.hi2, t1),
        _mm512_permutexvar_epi32(p.lo2, t1),
    );
    let t3 = sub16(
        _mm512_permutexvar_epi32(p.hi3, t2),
        _mm512_permutexvar_epi32(p.lo3, t2),
    );
    let g0 = _mm512_permutex2var_epi32(b, p.g0, t1);
    let g0 = _mm512_mask_permutexvar_epi32(g0, 1 << 14, p.g0t2, t2);
    let g1 = _mm512_maskz_permutex2var_epi32(0x07FF, t1, p.g1, t2);
    let g1 = _mm512_mask_mov_epi32(g1, 1 << 10, t3);
    (g0, g1)
}

/// A non-interpolated slot's grid: the taps in cells 0..8, everything else zero.
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn plain_grid(b: __m512i, p: &W3Perm) -> (__m512i, __m512i) {
    (
        _mm512_maskz_permutexvar_epi32(0x00FF, p.plain, b),
        _mm512_setzero_si512(),
    )
}

// ---------------------------------------------------------------------------
// AoS ext <-> limb-major transposes
// ---------------------------------------------------------------------------

/// Index tables of the ext transposes and the fold tap transpose.
#[derive(Clone, Copy)]
pub(crate) struct ExtPerm {
    /// limb `l` of AoS elements 0..8 out of two 4-element vectors
    limb: [__m512i; 4],
    /// `[L0[e], L1[e]]` interleave for `e = 0..8` / `8..16`
    x_lo: __m512i,
    x_hi: __m512i,
    /// `[X0, X1, Y0, Y1, ...]` merge for elements 0..4 / 4..8 of an X/Y pair
    z_lo: __m512i,
    z_hi: __m512i,
    /// fold transposes: taps 0..4 / 4..8 of a 2-vector row pair into
    /// `[tap][4 rows]`, then `[2 taps][8 rows]` merges
    fa: __m512i,
    fb: __m512i,
    fc: [__m512i; 2],
}

impl ExtPerm {
    #[target_feature(enable = "avx512f")]
    pub(crate) unsafe fn new() -> Self {
        let limb: [__m512i; 4] = core::array::from_fn(|l| {
            let t: [i32; 16] = core::array::from_fn(|e| (4 * (e % 8) + l) as i32);
            idx(&t)
        });
        let x_lo: [i32; 16] = core::array::from_fn(|i| {
            if i % 2 == 0 {
                (i / 2) as i32
            } else {
                16 + (i / 2) as i32
            }
        });
        let x_hi: [i32; 16] = core::array::from_fn(|i| {
            if i % 2 == 0 {
                8 + (i / 2) as i32
            } else {
                24 + (i / 2) as i32
            }
        });
        let z_lo: [i32; 16] = core::array::from_fn(|i| {
            let (e, l) = (i / 4, i % 4);
            if l < 2 {
                (2 * e + l) as i32
            } else {
                16 + (2 * e + l - 2) as i32
            }
        });
        let z_hi: [i32; 16] = core::array::from_fn(|i| {
            let (e, l) = (i / 4, i % 4);
            if l < 2 {
                (8 + 2 * e + l) as i32
            } else {
                16 + (8 + 2 * e + l - 2) as i32
            }
        });
        // stage 1 of the fold transpose: lane 4t + q = tap t of row q of the
        // pair (rows 0,1 in the first vector, 2,3 in the second)
        let fa: [i32; 16] = core::array::from_fn(|i| {
            let (t, q) = (i / 4, i % 4);
            [t, 8 + t, 16 + t, 24 + t][q] as i32
        });
        let fb: [i32; 16] = core::array::from_fn(|i| {
            let (t, q) = (i / 4 + 4, i % 4);
            [t, 8 + t, 16 + t, 24 + t][q] as i32
        });
        // stage 2: lane 8 t' + r = tap t' (of the pair {0,1} or {2,3}) of row r
        let fc: [__m512i; 2] = core::array::from_fn(|pair| {
            let t: [i32; 16] = core::array::from_fn(|i| {
                let (tp, r) = (i / 8 + 2 * pair, i % 8);
                if r < 4 {
                    (4 * tp + r) as i32
                } else {
                    (16 + 4 * tp + r - 4) as i32
                }
            });
            idx(&t)
        });
        Self {
            limb,
            x_lo: idx(&x_lo),
            x_hi: idx(&x_hi),
            z_lo: idx(&z_lo),
            z_hi: idx(&z_hi),
            fa: idx(&fa),
            fb: idx(&fb),
            fc,
        }
    }
}

/// 8 consecutive AoS ext elements -> limb-major (lanes 0..8 valid, lanes
/// 8..16 duplicates).
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn transpose_ext8(src: *const BabyBearExt4, p: &ExtPerm) -> [__m512i; 4] {
    let z0 = _mm512_loadu_si512(src as *const __m512i);
    let z1 = _mm512_loadu_si512(src.add(4) as *const __m512i);
    core::array::from_fn(|l| _mm512_permutex2var_epi32(z0, p.limb[l], z1))
}

/// 16 AoS ext elements (4 vectors) -> limb-major over 16 lanes.
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn transpose_ext16_vecs(z: &[__m512i; 4], p: &ExtPerm) -> [__m512i; 4] {
    core::array::from_fn(|l| {
        let a = _mm512_permutex2var_epi32(z[0], p.limb[l], z[1]);
        let b = _mm512_permutex2var_epi32(z[2], p.limb[l], z[3]);
        _mm512_inserti64x4::<1>(a, _mm512_castsi512_si256(b))
    })
}

/// Limb-major over 16 lanes -> 16 consecutive AoS ext elements.
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn store_ext16(limbs: &[__m512i; 4], dst: *mut BabyBearExt4, p: &ExtPerm) {
    let x = _mm512_permutex2var_epi32(limbs[0], p.x_lo, limbs[1]);
    let y = _mm512_permutex2var_epi32(limbs[2], p.x_lo, limbs[3]);
    let x2 = _mm512_permutex2var_epi32(limbs[0], p.x_hi, limbs[1]);
    let y2 = _mm512_permutex2var_epi32(limbs[2], p.x_hi, limbs[3]);
    let d = dst as *mut __m512i;
    _mm512_storeu_si512(d, _mm512_permutex2var_epi32(x, p.z_lo, y));
    _mm512_storeu_si512(d.add(1), _mm512_permutex2var_epi32(x, p.z_hi, y));
    _mm512_storeu_si512(d.add(2), _mm512_permutex2var_epi32(x2, p.z_lo, y2));
    _mm512_storeu_si512(d.add(3), _mm512_permutex2var_epi32(x2, p.z_hi, y2));
}

/// Output-store policy of the forward kernels: non-temporal 16-byte stores
/// (no read-for-ownership traffic; the buffers are 16-byte aligned) unless
/// env `FWD_NT=0` asks for plain stores.
pub(crate) fn nt_stores() -> bool {
    static FLAG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *FLAG.get_or_init(|| std::env::var("FWD_NT").map(|v| v != "0").unwrap_or(true))
}

/// [`store_ext16`] with non-temporal 16-byte stores (`dst` 16-byte aligned).
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn store_ext16_nt(limbs: &[__m512i; 4], dst: *mut BabyBearExt4, p: &ExtPerm) {
    let x = _mm512_permutex2var_epi32(limbs[0], p.x_lo, limbs[1]);
    let y = _mm512_permutex2var_epi32(limbs[2], p.x_lo, limbs[3]);
    let x2 = _mm512_permutex2var_epi32(limbs[0], p.x_hi, limbs[1]);
    let y2 = _mm512_permutex2var_epi32(limbs[2], p.x_hi, limbs[3]);
    let z = [
        _mm512_permutex2var_epi32(x, p.z_lo, y),
        _mm512_permutex2var_epi32(x, p.z_hi, y),
        _mm512_permutex2var_epi32(x2, p.z_lo, y2),
        _mm512_permutex2var_epi32(x2, p.z_hi, y2),
    ];
    let d = dst as *mut __m128i;
    for (i, v) in z.iter().enumerate() {
        _mm_stream_si128(d.add(4 * i), _mm512_castsi512_si128(*v));
        _mm_stream_si128(d.add(4 * i + 1), _mm512_extracti32x4_epi32::<1>(*v));
        _mm_stream_si128(d.add(4 * i + 2), _mm512_extracti32x4_epi32::<2>(*v));
        _mm_stream_si128(d.add(4 * i + 3), _mm512_extracti32x4_epi32::<3>(*v));
    }
}

/// Output store per the policy: [`store_ext16_nt`] or [`store_ext16`].
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn store_ext16_out(
    limbs: &[__m512i; 4],
    dst: *mut BabyBearExt4,
    p: &ExtPerm,
    nt: bool,
) {
    if nt {
        store_ext16_nt(limbs, dst, p)
    } else {
        store_ext16(limbs, dst, p)
    }
}

/// 16 u32 with non-temporal 16-byte stores (`p` 16-byte aligned).
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn st_nt16(p: *mut u32, v: __m512i) {
    let d = p as *mut __m128i;
    _mm_stream_si128(d, _mm512_castsi512_si128(v));
    _mm_stream_si128(d.add(1), _mm512_extracti32x4_epi32::<1>(v));
    _mm_stream_si128(d.add(2), _mm512_extracti32x4_epi32::<2>(v));
    _mm_stream_si128(d.add(3), _mm512_extracti32x4_epi32::<3>(v));
}

/// 16 rows x 8 base taps (`v[k]` = rows `2k, 2k+1`) -> 8 tap vectors over
/// the 16 rows.
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn transpose_taps16(v: &[__m512i; 8], p: &ExtPerm) -> [__m512i; 8] {
    let a: [__m512i; 4] =
        core::array::from_fn(|q| _mm512_permutex2var_epi32(v[2 * q], p.fa, v[2 * q + 1]));
    let b: [__m512i; 4] =
        core::array::from_fn(|q| _mm512_permutex2var_epi32(v[2 * q], p.fb, v[2 * q + 1]));
    let mut out = [_mm512_setzero_si512(); 8];
    for (half, src) in [(0usize, &a), (4usize, &b)] {
        for pair in 0..2 {
            // rows 0..8 from (src[0], src[1]), rows 8..16 from (src[2], src[3])
            let lo = _mm512_permutex2var_epi32(src[0], p.fc[pair], src[1]);
            let hi = _mm512_permutex2var_epi32(src[2], p.fc[pair], src[3]);
            out[half + 2 * pair] = _mm512_inserti64x4::<1>(lo, _mm512_castsi512_si256(hi));
            out[half + 2 * pair + 1] = _mm512_shuffle_i32x4::<0xEE>(lo, hi);
        }
    }
    out
}

/// Limb-major SoA groups (`[group][limb]` at `grid + 16*(4g+l)`) -> 32 AoS
/// ext values.
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn untranspose_grid_to_aos(
    grid: *const u32,
    out: *mut BabyBearExt4,
    p: &ExtPerm,
) {
    for g in 0..2 {
        let limbs: [__m512i; 4] = core::array::from_fn(|l| ld(grid.add(16 * (4 * g + l))));
        store_ext16(&limbs, out.add(16 * g), p);
    }
}

/// 16x16 `u32` transpose: `r[i]` = row `i` -> `out[c]` = column `c`
/// (unpack 32, unpack 64, two 128-bit lane shuffle stages; 64 shuffles).
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn transpose16(r: &[__m512i; 16]) -> [__m512i; 16] {
    let mut a = [_mm512_setzero_si512(); 16];
    for i in 0..8 {
        a[2 * i] = _mm512_unpacklo_epi32(r[2 * i], r[2 * i + 1]);
        a[2 * i + 1] = _mm512_unpackhi_epi32(r[2 * i], r[2 * i + 1]);
    }
    let mut b = [_mm512_setzero_si512(); 16];
    for i in 0..4 {
        b[4 * i] = _mm512_unpacklo_epi64(a[4 * i], a[4 * i + 2]);
        b[4 * i + 1] = _mm512_unpackhi_epi64(a[4 * i], a[4 * i + 2]);
        b[4 * i + 2] = _mm512_unpacklo_epi64(a[4 * i + 1], a[4 * i + 3]);
        b[4 * i + 3] = _mm512_unpackhi_epi64(a[4 * i + 1], a[4 * i + 3]);
    }
    // b[4i + c] lane L = column 4L + c of rows 4i..4i+4
    let mut out = [_mm512_setzero_si512(); 16];
    for c in 0..4 {
        let x0 = _mm512_shuffle_i32x4::<0x44>(b[c], b[4 + c]);
        let x1 = _mm512_shuffle_i32x4::<0xEE>(b[c], b[4 + c]);
        let y0 = _mm512_shuffle_i32x4::<0x44>(b[8 + c], b[12 + c]);
        let y1 = _mm512_shuffle_i32x4::<0xEE>(b[8 + c], b[12 + c]);
        out[c] = _mm512_shuffle_i32x4::<0x88>(x0, y0);
        out[4 + c] = _mm512_shuffle_i32x4::<0xDD>(x0, y0);
        out[8 + c] = _mm512_shuffle_i32x4::<0x88>(x1, y1);
        out[12 + c] = _mm512_shuffle_i32x4::<0xDD>(x1, y1);
    }
    out
}

/// Modular sum of the 16 canonical lanes.
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn hsum_mod(v: __m512i) -> u32 {
    let v = add16(v, _mm512_shuffle_i32x4::<0x4E>(v, v));
    let v = add16(v, _mm512_shuffle_i32x4::<0xB1>(v, v));
    let v = add16(v, _mm512_shuffle_epi32::<0x4E>(v));
    let v = add16(v, _mm512_shuffle_epi32::<0xB1>(v));
    _mm_cvtsi128_si32(_mm512_castsi512_si128(v)) as u32
}

/// A right operand prepared for repeated lazy products (`limbs 1..3`
/// pre-scaled by 11, odd-lane halves precomputed).
#[derive(Clone, Copy)]
pub(crate) struct LazyRhs {
    b: [__m512i; 4],
    bh: [__m512i; 4],
    s: [__m512i; 3],
    sh: [__m512i; 3],
}
impl LazyRhs {
    #[inline]
    #[target_feature(enable = "avx512f")]
    pub(crate) unsafe fn new(b: &[__m512i; 4], r11: __m512i) -> Self {
        let s = [
            mont_mul16(b[1], r11),
            mont_mul16(b[2], r11),
            mont_mul16(b[3], r11),
        ];
        LazyRhs {
            b: *b,
            bh: core::array::from_fn(|i| hi64(b[i])),
            s,
            sh: core::array::from_fn(|i| hi64(s[i])),
        }
    }
}

/// `acc[l] += (a (x) rhs)_l` lazily: four raw products per limb with a
/// conditional subtraction after every two, so a long-lived accumulator
/// keeps its `< R P` invariant. `ah` = odd-lane halves of `a`.
#[inline]
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn lazy_mul_acc(
    acc: &mut [Lazy16; 4],
    a: &[__m512i; 4],
    ah: &[__m512i; 4],
    t: &LazyRhs,
) {
    // out0 = a0 b0 + a1 (11 b1) + a2 (11 b3) + a3 (11 b2)
    acc[0].mla_raw(a[0], ah[0], t.b[0], t.bh[0]);
    acc[0].mla_raw(a[1], ah[1], t.s[0], t.sh[0]);
    acc[0].condsub();
    acc[0].mla_raw(a[2], ah[2], t.s[2], t.sh[2]);
    acc[0].mla_raw(a[3], ah[3], t.s[1], t.sh[1]);
    acc[0].condsub();
    // out1 = a0 b1 + a1 b0 + a2 b2 + a3 (11 b3)
    acc[1].mla_raw(a[0], ah[0], t.b[1], t.bh[1]);
    acc[1].mla_raw(a[1], ah[1], t.b[0], t.bh[0]);
    acc[1].condsub();
    acc[1].mla_raw(a[2], ah[2], t.b[2], t.bh[2]);
    acc[1].mla_raw(a[3], ah[3], t.s[2], t.sh[2]);
    acc[1].condsub();
    // out2 = a0 b2 + a2 b0 + a1 (11 b3) + a3 (11 b1)
    acc[2].mla_raw(a[0], ah[0], t.b[2], t.bh[2]);
    acc[2].mla_raw(a[2], ah[2], t.b[0], t.bh[0]);
    acc[2].condsub();
    acc[2].mla_raw(a[1], ah[1], t.s[2], t.sh[2]);
    acc[2].mla_raw(a[3], ah[3], t.s[0], t.sh[0]);
    acc[2].condsub();
    // out3 = a0 b3 + a1 b2 + a2 b1 + a3 b0
    acc[3].mla_raw(a[0], ah[0], t.b[3], t.bh[3]);
    acc[3].mla_raw(a[1], ah[1], t.b[2], t.bh[2]);
    acc[3].condsub();
    acc[3].mla_raw(a[2], ah[2], t.b[1], t.bh[1]);
    acc[3].mla_raw(a[3], ah[3], t.b[0], t.bh[0]);
    acc[3].condsub();
}

/// One LSB folding step over AoS `Ext4` pairs: `dst[i] = src[2i] + ch *
/// (src[2i+1] - src[2i])` for `i < n_pairs` — 16 pairs per iteration (32
/// elements loaded as two SoA groups, even/odd lanes split by a two-source
/// permute), scalar tail. The WHIR eq-poly fold of the X86 GKR backend.
#[target_feature(enable = "avx512f")]
pub(crate) unsafe fn fold_pairs_avx512(
    src: *const BabyBearExt4,
    n_pairs: usize,
    ch: &BabyBearExt4,
    dst: *mut BabyBearExt4,
) {
    let p = ExtPerm::new();
    let chl = bcast_ext(ch);
    let r11 = r11v();
    let ev = idx(&[0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30]);
    let od = idx(&[1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31]);
    let full = n_pairs / 16;
    for blk in 0..full {
        let s = src.add(blk * 32) as *const u32;
        let z: [__m512i; 8] = core::array::from_fn(|k| ld(s.add(k * 16)));
        let la = transpose_ext16_vecs(&[z[0], z[1], z[2], z[3]], &p);
        let lb = transpose_ext16_vecs(&[z[4], z[5], z[6], z[7]], &p);
        let a: [__m512i; 4] = core::array::from_fn(|l| _mm512_permutex2var_epi32(la[l], ev, lb[l]));
        let b: [__m512i; 4] = core::array::from_fn(|l| _mm512_permutex2var_epi32(la[l], od, lb[l]));
        let d: [__m512i; 4] = core::array::from_fn(|l| sub16(b[l], a[l]));
        let prod = soa_ext_mul(&d, &chl, r11);
        let out: [__m512i; 4] = core::array::from_fn(|l| add16(a[l], prod[l]));
        store_ext16(&out, dst.add(blk * 16), &p);
    }
    for i in full * 16..n_pairs {
        let a = *src.add(2 * i);
        let mut t = *src.add(2 * i + 1);
        t.sub_assign(&a);
        t.mul_assign(ch);
        t.add_assign(&a);
        dst.add(i).write(t);
    }
}
