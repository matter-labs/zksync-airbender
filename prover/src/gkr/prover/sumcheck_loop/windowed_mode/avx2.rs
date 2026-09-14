//! x86-64 AVX2 kernels for the windowed-sumcheck hot loops, specialized for
//! `BabyBearField` / `BabyBearExt4` (Montgomery form, `Ext4` = 4 contiguous
//! Montgomery `u32` limbs) — the twin of the aarch64 `neon` module.
//!
//! Lane conventions:
//! * "elem2" kernels hold TWO `Ext4` elements per `__m256i` (one per 128-bit
//!   half); every shuffle is in-lane, so both elements are processed by the
//!   same instruction stream (`ext_mul2`, `mat_mul2`);
//! * "SoA" kernels hold 8 consecutive CELLS of one row per vector, one vector
//!   per limb: a cell group is `[4 limbs][8 cells]` (32 u32), a base cell
//!   group `[8 cells]`. The lazy u64 accumulators keep the products of the
//!   even and odd cells in two separate vectors (the natural `vpmuludq`
//!   output) and merge them back at REDC time.
//!
//! All lane arithmetic follows the scalar implementations exactly: canonical
//! Montgomery products (`a*b + m*p` in 64-bit lanes, high-word merge, one
//! conditional subtract), the flat quartic `Ext4` table with `alpha^2 = 11`,
//! `beta^2 = alpha`. Lazy accumulation adds raw `< P^2` products and keeps
//! `X < R*P` by a conditional `R*P` subtraction after every two products, so
//! one REDC + canonicalization per row is exact — outputs are byte-identical
//! to the scalar kernels.

use core::arch::x86_64::*;

use ::field::baby_bear::base::BabyBearField;
use ::field::baby_bear::ext4::BabyBearExt4;
use ::field::{Field, PrimeField};

pub(crate) const P: u32 = 0x78000001;
pub(crate) const K: u32 = 0x77ffffff; // -P^{-1} mod 2^32 (matches BabyBearField::MONT_K)
const RP: u64 = (P as u64) << 32;

#[inline(always)]
unsafe fn pv() -> __m256i {
    _mm256_set1_epi32(P as i32)
}
#[inline(always)]
unsafe fn kv() -> __m256i {
    _mm256_set1_epi32(K as i32)
}

/// Canonical Montgomery product on 8 lanes.
#[inline(always)]
pub(crate) unsafe fn mont_mul8(a: __m256i, b: __m256i) -> __m256i {
    let lo = _mm256_mullo_epi32(a, b);
    let m = _mm256_mullo_epi32(lo, kv());
    let prod_e = _mm256_mul_epu32(a, b);
    let prod_o = _mm256_mul_epu32(_mm256_srli_epi64::<32>(a), _mm256_srli_epi64::<32>(b));
    let mp_e = _mm256_mul_epu32(m, pv());
    let mp_o = _mm256_mul_epu32(_mm256_srli_epi64::<32>(m), pv());
    let t_e = _mm256_add_epi64(prod_e, mp_e);
    let t_o = _mm256_add_epi64(prod_o, mp_o);
    let r = _mm256_blend_epi32::<0b1010_1010>(_mm256_srli_epi64::<32>(t_e), t_o);
    _mm256_min_epu32(r, _mm256_sub_epi32(r, pv()))
}

#[inline(always)]
pub(crate) unsafe fn add8(a: __m256i, b: __m256i) -> __m256i {
    let s = _mm256_add_epi32(a, b);
    _mm256_min_epu32(s, _mm256_sub_epi32(s, pv()))
}

#[inline(always)]
pub(crate) unsafe fn sub8(a: __m256i, b: __m256i) -> __m256i {
    let d = _mm256_sub_epi32(a, b);
    _mm256_min_epu32(d, _mm256_add_epi32(d, pv()))
}

/// Montgomery form of 11 (the quadratic non-residue of the tower).
#[inline(always)]
pub(crate) fn r11() -> u32 {
    BabyBearField::new(11).raw_u32_value()
}

#[inline(always)]
pub(crate) unsafe fn r11v() -> __m256i {
    _mm256_set1_epi32(r11() as i32)
}

#[inline(always)]
pub(crate) unsafe fn bc32(x: u32) -> __m256i {
    _mm256_set1_epi32(x as i32)
}

// per-128-bit-lane broadcasts of dword k
#[inline(always)]
unsafe fn lane0(a: __m256i) -> __m256i {
    _mm256_shuffle_epi32::<0x00>(a)
}
#[inline(always)]
unsafe fn lane1(a: __m256i) -> __m256i {
    _mm256_shuffle_epi32::<0x55>(a)
}
#[inline(always)]
unsafe fn lane2(a: __m256i) -> __m256i {
    _mm256_shuffle_epi32::<0xAA>(a)
}
#[inline(always)]
unsafe fn lane3(a: __m256i) -> __m256i {
    _mm256_shuffle_epi32::<0xFF>(a)
}

/// Two consecutive `Ext4` elements.
#[inline(always)]
pub(crate) unsafe fn load2(p: *const BabyBearExt4) -> __m256i {
    _mm256_loadu_si256(p as *const __m256i)
}
#[inline(always)]
pub(crate) unsafe fn store2(p: *mut BabyBearExt4, v: __m256i) {
    _mm256_storeu_si256(p as *mut __m256i, v)
}
/// One element into the low half (upper half zero).
#[inline(always)]
pub(crate) unsafe fn load1(p: *const BabyBearExt4) -> __m256i {
    _mm256_zextsi128_si256(_mm_loadu_si128(p as *const __m128i))
}
#[inline(always)]
pub(crate) unsafe fn store1(p: *mut BabyBearExt4, v: __m256i) {
    _mm_storeu_si128(p as *mut __m128i, _mm256_castsi256_si128(v))
}
/// One element in both halves.
#[inline(always)]
pub(crate) unsafe fn bcast_elem(v: &BabyBearExt4) -> __m256i {
    _mm256_broadcastsi128_si256(_mm_loadu_si128(v as *const BabyBearExt4 as *const __m128i))
}
/// `[a.lo | b.lo]` / `[a.hi | b.hi]`.
#[inline(always)]
pub(crate) unsafe fn lows(a: __m256i, b: __m256i) -> __m256i {
    _mm256_permute2x128_si256::<0x20>(a, b)
}
#[inline(always)]
pub(crate) unsafe fn highs(a: __m256i, b: __m256i) -> __m256i {
    _mm256_permute2x128_si256::<0x31>(a, b)
}
/// `[a.lo | a.lo]` / `[a.hi | a.hi]`.
#[inline(always)]
pub(crate) unsafe fn dup_lo(a: __m256i) -> __m256i {
    _mm256_permute2x128_si256::<0x00>(a, a)
}
#[inline(always)]
pub(crate) unsafe fn dup_hi(a: __m256i) -> __m256i {
    _mm256_permute2x128_si256::<0x11>(a, a)
}

/// The three permuted/scaled columns of `b` (per half): `col1 = [11b1, b0,
/// 11b3, b2]`, `col2 = [11b3, b2, b0, b1]`, `col3 = [11b2, 11b3, 11b1, b0]`.
#[inline(always)]
unsafe fn ext_cols(b: __m256i, r11v: __m256i) -> [__m256i; 4] {
    let e = mont_mul8(b, r11v); // [11b0, 11b1, 11b2, 11b3]
    let col1 = _mm256_blend_epi32::<0b1010_1010>(
        _mm256_shuffle_epi32::<0xF5>(e), // [11b1, 11b1, 11b3, 11b3]
        _mm256_shuffle_epi32::<0xA0>(b), // [b0, b0, b2, b2]
    );
    let col2 = _mm256_alignr_epi8::<8>(b, col1); // [col1[2], col1[3], b[0], b[1]]
    let col3 = _mm256_alignr_epi8::<8>(col1, e); // [e[2], e[3], col1[0], col1[1]]
    [b, col1, col2, col3]
}

/// `a (x) b` on both halves independently (two variable `Ext4` products).
#[inline(always)]
pub(crate) unsafe fn ext_mul2(a: __m256i, b: __m256i, r11v: __m256i) -> __m256i {
    let cols = ext_cols(b, r11v);
    let mut acc = mont_mul8(lane0(a), cols[0]);
    acc = add8(acc, mont_mul8(lane1(a), cols[1]));
    acc = add8(acc, mont_mul8(lane2(a), cols[2]));
    add8(acc, mont_mul8(lane3(a), cols[3]))
}

/// Precomputed column form of a fixed `Ext4` multiplier, duplicated in both
/// halves: `mat_mul2(m(b), a) = a (x) b` on both elements of `a`.
#[derive(Clone, Copy)]
pub(crate) struct ExtMatrix2 {
    cols: [__m256i; 4],
}

impl ExtMatrix2 {
    #[inline(always)]
    pub(crate) fn new(b: &BabyBearExt4) -> Self {
        unsafe {
            ExtMatrix2 {
                cols: ext_cols(bcast_elem(b), r11v()),
            }
        }
    }
}

#[inline(always)]
pub(crate) unsafe fn mat_mul2(m: &ExtMatrix2, a: __m256i) -> __m256i {
    let mut acc = mont_mul8(lane0(a), m.cols[0]);
    acc = add8(acc, mont_mul8(lane1(a), m.cols[1]));
    acc = add8(acc, mont_mul8(lane2(a), m.cols[2]));
    add8(acc, mont_mul8(lane3(a), m.cols[3]))
}

// ---------------------------------------------------------------------------
// transposes
// ---------------------------------------------------------------------------

/// 8 AoS ext elements (`v[i] = [e_{2i} | e_{2i+1}]`) -> limb-major
/// `[4 limbs][8 elements]`.
#[inline(always)]
pub(crate) unsafe fn transpose_8x4(
    v0: __m256i,
    v1: __m256i,
    v2: __m256i,
    v3: __m256i,
) -> [__m256i; 4] {
    let t0 = _mm256_unpacklo_epi32(v0, v1);
    let t1 = _mm256_unpackhi_epi32(v0, v1);
    let t2 = _mm256_unpacklo_epi32(v2, v3);
    let t3 = _mm256_unpackhi_epi32(v2, v3);
    let u0 = _mm256_unpacklo_epi64(t0, t2);
    let u1 = _mm256_unpackhi_epi64(t0, t2);
    let u2 = _mm256_unpacklo_epi64(t1, t3);
    let u3 = _mm256_unpackhi_epi64(t1, t3);
    let idx = _mm256_setr_epi32(0, 4, 1, 5, 2, 6, 3, 7);
    [
        _mm256_permutevar8x32_epi32(u0, idx),
        _mm256_permutevar8x32_epi32(u1, idx),
        _mm256_permutevar8x32_epi32(u2, idx),
        _mm256_permutevar8x32_epi32(u3, idx),
    ]
}

/// Inverse of [`transpose_8x4`]: limb-major -> 4 vectors of 2 AoS elements.
#[inline(always)]
pub(crate) unsafe fn untranspose_4x8(l: &[__m256i; 4]) -> [__m256i; 4] {
    let idx = _mm256_setr_epi32(0, 2, 4, 6, 1, 3, 5, 7);
    let w0 = _mm256_permutevar8x32_epi32(l[0], idx);
    let w1 = _mm256_permutevar8x32_epi32(l[1], idx);
    let w2 = _mm256_permutevar8x32_epi32(l[2], idx);
    let w3 = _mm256_permutevar8x32_epi32(l[3], idx);
    let p0 = _mm256_unpacklo_epi32(w0, w1);
    let p1 = _mm256_unpacklo_epi32(w2, w3);
    let p2 = _mm256_unpackhi_epi32(w0, w1);
    let p3 = _mm256_unpackhi_epi32(w2, w3);
    [
        _mm256_unpacklo_epi64(p0, p1),
        _mm256_unpackhi_epi64(p0, p1),
        _mm256_unpacklo_epi64(p2, p3),
        _mm256_unpackhi_epi64(p2, p3),
    ]
}

/// 8x8 u32 transpose: `r[i]` = row i (8 columns) -> `out[c]` = column c
/// over the 8 rows.
#[inline(always)]
pub(crate) unsafe fn transpose_8x8(r: &[__m256i; 8]) -> [__m256i; 8] {
    let a0 = _mm256_unpacklo_epi32(r[0], r[1]);
    let a1 = _mm256_unpackhi_epi32(r[0], r[1]);
    let a2 = _mm256_unpacklo_epi32(r[2], r[3]);
    let a3 = _mm256_unpackhi_epi32(r[2], r[3]);
    let a4 = _mm256_unpacklo_epi32(r[4], r[5]);
    let a5 = _mm256_unpackhi_epi32(r[4], r[5]);
    let a6 = _mm256_unpacklo_epi32(r[6], r[7]);
    let a7 = _mm256_unpackhi_epi32(r[6], r[7]);
    let b0 = _mm256_unpacklo_epi64(a0, a2);
    let b1 = _mm256_unpackhi_epi64(a0, a2);
    let b2 = _mm256_unpacklo_epi64(a1, a3);
    let b3 = _mm256_unpackhi_epi64(a1, a3);
    let b4 = _mm256_unpacklo_epi64(a4, a6);
    let b5 = _mm256_unpackhi_epi64(a4, a6);
    let b6 = _mm256_unpacklo_epi64(a5, a7);
    let b7 = _mm256_unpackhi_epi64(a5, a7);
    [
        _mm256_permute2x128_si256::<0x20>(b0, b4),
        _mm256_permute2x128_si256::<0x20>(b1, b5),
        _mm256_permute2x128_si256::<0x20>(b2, b6),
        _mm256_permute2x128_si256::<0x20>(b3, b7),
        _mm256_permute2x128_si256::<0x31>(b0, b4),
        _mm256_permute2x128_si256::<0x31>(b1, b5),
        _mm256_permute2x128_si256::<0x31>(b2, b6),
        _mm256_permute2x128_si256::<0x31>(b3, b7),
    ]
}

/// 8 consecutive AoS ext elements -> limb-major SoA cell.
#[inline(always)]
pub(crate) unsafe fn soa_transpose_ext8(src: *const BabyBearExt4) -> [__m256i; 4] {
    transpose_8x4(
        load2(src),
        load2(src.add(2)),
        load2(src.add(4)),
        load2(src.add(6)),
    )
}

/// 8 AoS ext elements at element stride `stride` -> limb-major SoA cell.
#[inline(always)]
pub(crate) unsafe fn soa_transpose_ext8_strided(
    src: *const BabyBearExt4,
    stride: usize,
) -> [__m256i; 4] {
    let pair = |i: usize| {
        _mm256_set_m128i(
            _mm_loadu_si128(src.add((i + 1) * stride) as *const __m128i),
            _mm_loadu_si128(src.add(i * stride) as *const __m128i),
        )
    };
    transpose_8x4(pair(0), pair(2), pair(4), pair(6))
}

/// Inverse of [`soa_transpose_ext8`]: limb-major cell -> 8 AoS ext elements.
#[inline(always)]
pub(crate) unsafe fn soa_store_ext8(limbs: &[__m256i; 4], dst: *mut BabyBearExt4) {
    let v = untranspose_4x8(limbs);
    store2(dst, v[0]);
    store2(dst.add(2), v[1]);
    store2(dst.add(4), v[2]);
    store2(dst.add(6), v[3]);
}

/// Load / store one SoA cell (4 limb vectors) from a raw grid buffer.
#[inline(always)]
pub(crate) unsafe fn soa_load_cell(src: *const u32) -> [__m256i; 4] {
    core::array::from_fn(|l| _mm256_loadu_si256(src.add(8 * l) as *const __m256i))
}
#[inline(always)]
pub(crate) unsafe fn soa_store_cell(dst: *mut u32, v: &[__m256i; 4]) {
    for l in 0..4 {
        _mm256_storeu_si256(dst.add(8 * l) as *mut __m256i, v[l]);
    }
}
#[inline(always)]
pub(crate) unsafe fn ld(p: *const u32) -> __m256i {
    _mm256_loadu_si256(p as *const __m256i)
}
#[inline(always)]
pub(crate) unsafe fn st(p: *mut u32, v: __m256i) {
    _mm256_storeu_si256(p as *mut __m256i, v)
}

/// Broadcast the limbs of one ext value to cell vectors.
#[inline(always)]
pub(crate) unsafe fn soa_broadcast_ext(v: &BabyBearExt4) -> [__m256i; 4] {
    let limbs: [u32; 4] = core::mem::transmute(*v);
    core::array::from_fn(|l| bc32(limbs[l]))
}

/// Cell-pointwise `Ext4` multiplication in SoA form (flat quartic table).
#[inline(always)]
pub(crate) unsafe fn soa_ext_mul(
    a: &[__m256i; 4],
    b: &[__m256i; 4],
    r11v: __m256i,
) -> [__m256i; 4] {
    let p00 = mont_mul8(a[0], b[0]);
    let p01 = mont_mul8(a[0], b[1]);
    let p02 = mont_mul8(a[0], b[2]);
    let p03 = mont_mul8(a[0], b[3]);
    let p10 = mont_mul8(a[1], b[0]);
    let p11 = mont_mul8(a[1], b[1]);
    let p12 = mont_mul8(a[1], b[2]);
    let p13 = mont_mul8(a[1], b[3]);
    let p20 = mont_mul8(a[2], b[0]);
    let p21 = mont_mul8(a[2], b[1]);
    let p22 = mont_mul8(a[2], b[2]);
    let p23 = mont_mul8(a[2], b[3]);
    let p30 = mont_mul8(a[3], b[0]);
    let p31 = mont_mul8(a[3], b[1]);
    let p32 = mont_mul8(a[3], b[2]);
    let p33 = mont_mul8(a[3], b[3]);
    let out0 = add8(p00, mont_mul8(add8(add8(p11, p23), p32), r11v));
    let out1 = add8(add8(p01, p10), add8(p22, mont_mul8(p33, r11v)));
    let out2 = add8(add8(p02, p20), mont_mul8(add8(p13, p31), r11v));
    let out3 = add8(add8(p03, p12), add8(p21, p30));
    [out0, out1, out2, out3]
}

// ---------------------------------------------------------------------------
// lazy u64 accumulation (8 cells per limb: even-cell and odd-cell products)
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
pub(crate) struct LazyLimb {
    e: __m256i,
    o: __m256i,
}

impl LazyLimb {
    #[inline(always)]
    pub(crate) unsafe fn zero() -> Self {
        LazyLimb {
            e: _mm256_setzero_si256(),
            o: _mm256_setzero_si256(),
        }
    }
    #[inline(always)]
    pub(crate) unsafe fn load(p: *const u64) -> Self {
        LazyLimb {
            e: _mm256_loadu_si256(p as *const __m256i),
            o: _mm256_loadu_si256(p.add(4) as *const __m256i),
        }
    }
    #[inline(always)]
    pub(crate) unsafe fn store(&self, p: *mut u64) {
        _mm256_storeu_si256(p as *mut __m256i, self.e);
        _mm256_storeu_si256(p.add(4) as *mut __m256i, self.o);
    }
    #[inline(always)]
    pub(crate) unsafe fn store_zero(p: *mut u64) {
        _mm256_storeu_si256(p as *mut __m256i, _mm256_setzero_si256());
        _mm256_storeu_si256(p.add(4) as *mut __m256i, _mm256_setzero_si256());
    }
    /// `+= coeff * v` lane-wise (raw 64-bit products).
    #[inline(always)]
    pub(crate) unsafe fn mla(&mut self, coeff: __m256i, v: __m256i) {
        self.e = _mm256_add_epi64(self.e, _mm256_mul_epu32(coeff, v));
        self.o = _mm256_add_epi64(
            self.o,
            _mm256_mul_epu32(_mm256_srli_epi64::<32>(coeff), _mm256_srli_epi64::<32>(v)),
        );
    }
    #[inline(always)]
    unsafe fn condsub_one(x: __m256i) -> __m256i {
        let rp = _mm256_set1_epi64x(RP as i64);
        let flip = _mm256_set1_epi64x(i64::MIN);
        // unsigned x >= RP  <=>  signed (x ^ 2^63) > ((RP - 1) ^ 2^63)
        let mask = _mm256_cmpgt_epi64(
            _mm256_xor_si256(x, flip),
            _mm256_set1_epi64x(((RP - 1) as i64) ^ i64::MIN),
        );
        _mm256_sub_epi64(x, _mm256_and_si256(mask, rp))
    }
    #[inline(always)]
    pub(crate) unsafe fn condsub(&mut self) {
        self.e = Self::condsub_one(self.e);
        self.o = Self::condsub_one(self.o);
    }
    /// One conditional `R*P` subtraction, REDC and canonicalization.
    #[inline(always)]
    pub(crate) unsafe fn redc(mut self) -> __m256i {
        self.condsub();
        let m_e = _mm256_mullo_epi32(self.e, kv());
        let m_o = _mm256_mullo_epi32(self.o, kv());
        let s_e = _mm256_add_epi64(self.e, _mm256_mul_epu32(m_e, pv()));
        let s_o = _mm256_add_epi64(self.o, _mm256_mul_epu32(m_o, pv()));
        let r = _mm256_blend_epi32::<0b1010_1010>(_mm256_srli_epi64::<32>(s_e), s_o);
        _mm256_min_epu32(r, _mm256_sub_epi32(r, pv()))
    }
}

/// lazy buffer offset (u64 elements) of limb `l` of cell group `g`
#[inline(always)]
pub(crate) const fn lazy_off(g: usize, l: usize) -> usize {
    32 * g + 8 * l
}
/// u32 offset of limb `l` of cell group `g` in an ext SoA grid
#[inline(always)]
pub(crate) const fn ext_off(g: usize, l: usize) -> usize {
    32 * g + 8 * l
}

/// `acc[cell] += coeff * (a[cell] * b[cell])` over N base cell groups, lazily.
#[inline(always)]
pub(crate) unsafe fn soa_quad_bb_lazy<const N: usize>(
    acc: *mut u64,
    a: *const u32,
    b: *const u32,
    coeff: &BabyBearExt4,
) {
    let climbs: [u32; 4] = core::mem::transmute(*coeff);
    let cv: [__m256i; 4] = core::array::from_fn(|l| bc32(climbs[l]));
    for g in 0..N {
        let t = mont_mul8(ld(a.add(8 * g)), ld(b.add(8 * g)));
        for l in 0..4 {
            let p = acc.add(lazy_off(g, l));
            let mut x = LazyLimb::load(p);
            x.mla(cv[l], t);
            x.store(p);
        }
    }
}

/// `acc[cell] += coeff * a[cell]` over the first N base cell groups, lazily.
#[inline(always)]
pub(crate) unsafe fn soa_lin_base_all_n<const N: usize>(
    acc: *mut u64,
    a: *const u32,
    coeff: &BabyBearExt4,
) {
    let climbs: [u32; 4] = core::mem::transmute(*coeff);
    let cv: [__m256i; 4] = core::array::from_fn(|l| bc32(climbs[l]));
    for g in 0..N {
        let t = ld(a.add(8 * g));
        for l in 0..4 {
            let p = acc.add(lazy_off(g, l));
            let mut x = LazyLimb::load(p);
            x.mla(cv[l], t);
            x.store(p);
        }
    }
}

/// Conditional `R*P` subtraction over the whole lazy accumulator.
#[inline(always)]
pub(crate) unsafe fn soa_lazy_condsub<const N: usize>(acc: *mut u64) {
    for g in 0..N {
        for l in 0..4 {
            let p = acc.add(lazy_off(g, l));
            let mut x = LazyLimb::load(p);
            x.condsub();
            x.store(p);
        }
    }
}

/// Final REDC + canonicalization of the lazy accumulator into canonical SoA
/// u32 cells; zeroes the accumulator.
#[inline(always)]
pub(crate) unsafe fn soa_lazy_finalize<const N: usize>(acc: *mut u64, out: *mut u32) {
    for g in 0..N {
        for l in 0..4 {
            let p = acc.add(lazy_off(g, l));
            let r = LazyLimb::load(p).redc();
            st(out.add(ext_off(g, l)), r);
            LazyLimb::store_zero(p);
        }
    }
}

/// `dst[cell] += coeff (x) (a_ext[cell] * b_base[cell])` over N cell groups.
#[inline(always)]
pub(crate) unsafe fn soa_quad_be<const N: usize>(
    dst: *mut u32,
    a_ext: *const u32,
    b_base: *const u32,
    coeff_bcast: &[__m256i; 4],
    r11v: __m256i,
) {
    for g in 0..N {
        let bv = ld(b_base.add(8 * g));
        let t: [__m256i; 4] = core::array::from_fn(|l| mont_mul8(ld(a_ext.add(ext_off(g, l))), bv));
        let w = soa_ext_mul(&t, coeff_bcast, r11v);
        for l in 0..4 {
            let p = dst.add(ext_off(g, l));
            st(p, add8(ld(p), w[l]));
        }
    }
}

/// `dst[cell] += coeff (x) (a[cell] (x) b[cell])` over N ext cell groups.
#[inline(always)]
pub(crate) unsafe fn soa_quad_ee_n<const N: usize>(
    dst: *mut u32,
    a: *const u32,
    b: *const u32,
    coeff_bcast: &[__m256i; 4],
    r11v: __m256i,
) {
    for g in 0..N {
        let av = soa_load_cell(a.add(32 * g));
        let bv = soa_load_cell(b.add(32 * g));
        let v = soa_ext_mul(&av, &bv, r11v);
        let w = soa_ext_mul(&v, coeff_bcast, r11v);
        for l in 0..4 {
            let p = dst.add(ext_off(g, l));
            st(p, add8(ld(p), w[l]));
        }
    }
}

/// `dst[cell] += coeff (x) a_ext[cell]` over the first N ext cell groups.
#[inline(always)]
pub(crate) unsafe fn soa_lin_ext_all_n<const N: usize>(
    dst: *mut u32,
    a_ext: *const u32,
    coeff_bcast: &[__m256i; 4],
    r11v: __m256i,
) {
    for g in 0..N {
        let av = soa_load_cell(a_ext.add(32 * g));
        let w = soa_ext_mul(&av, coeff_bcast, r11v);
        for l in 0..4 {
            let p = dst.add(ext_off(g, l));
            st(p, add8(ld(p), w[l]));
        }
    }
}

/// `dst[cell] += constant` over the first N ext cell groups.
#[inline(always)]
pub(crate) unsafe fn soa_add_const_all_n<const N: usize>(
    dst: *mut u32,
    const_bcast: &[__m256i; 4],
) {
    for g in 0..N {
        for l in 0..4 {
            let p = dst.add(ext_off(g, l));
            st(p, add8(ld(p), const_bcast[l]));
        }
    }
}

/// `acc[cell] += (lazy_out[cell] + reduced[cell]) (x) eq` over N groups;
/// zeroes `reduced`.
#[inline(always)]
pub(crate) unsafe fn soa_apply_eq_and_accumulate<const N: usize>(
    acc: *mut u32,
    lazy_out: *const u32,
    reduced: *mut u32,
    eq_soa: &[__m256i; 4],
    r11v: __m256i,
) {
    for g in 0..N {
        let v: [__m256i; 4] = core::array::from_fn(|l| {
            add8(
                ld(lazy_out.add(ext_off(g, l))),
                ld(reduced.add(ext_off(g, l))),
            )
        });
        let w = soa_ext_mul(&v, eq_soa, r11v);
        for l in 0..4 {
            let p = acc.add(ext_off(g, l));
            st(p, add8(ld(p), w[l]));
            st(reduced.add(ext_off(g, l)), _mm256_setzero_si256());
        }
    }
}

/// `acc[cell] += eval[cell] (x) eq` over N groups; zeroes `eval`.
#[inline(always)]
pub(crate) unsafe fn soa_apply_eq_and_accumulate_n<const N: usize>(
    acc: *mut u32,
    eval: *mut u32,
    eq_soa: &[__m256i; 4],
    r11v: __m256i,
) {
    for g in 0..N {
        let v = soa_load_cell(eval.add(32 * g));
        let w = soa_ext_mul(&v, eq_soa, r11v);
        for l in 0..4 {
            let p = acc.add(ext_off(g, l));
            st(p, add8(ld(p), w[l]));
            st(eval.add(ext_off(g, l)), _mm256_setzero_si256());
        }
    }
}

/// Per-tap multiplication table of a fixed ext multiplier `p`, broadcast to
/// cell vectors: `(p (x) v)_j = sum_k m[j][k] * v_k` with canonical entries
/// (the `11*p_i` entries REDC'd once at build time), lazy-accumulable.
#[derive(Clone, Copy)]
pub(crate) struct SoaExtTable {
    pub(crate) m: [[__m256i; 4]; 4],
}

impl SoaExtTable {
    #[inline(always)]
    pub(crate) fn new(p: &BabyBearExt4) -> Self {
        let l: [u32; 4] = unsafe { core::mem::transmute(*p) };
        let e11 = BabyBearField::new(11);
        let scaled: [u32; 4] = core::array::from_fn(|i| {
            let mut t = BabyBearField::from_raw_u32(l[i]);
            t.mul_assign(&e11);
            t.raw_u32_value()
        });
        let rows: [[u32; 4]; 4] = [
            [l[0], scaled[1], scaled[3], scaled[2]],
            [l[1], l[0], l[2], scaled[3]],
            [l[2], scaled[3], l[0], scaled[1]],
            [l[3], l[2], l[1], l[0]],
        ];
        SoaExtTable {
            m: unsafe { core::array::from_fn(|j| core::array::from_fn(|k| bc32(rows[j][k]))) },
        }
    }
}

/// `lazy[cell] += coeff (x) (a[cell] (x) b[cell])` over N ext cell groups
/// with the coefficient multiply deferred into the lazy accumulator.
#[inline(always)]
pub(crate) unsafe fn soa_quad_ee_lazy<const N: usize>(
    lazy: *mut u64,
    a: *const u32,
    b: *const u32,
    table: &SoaExtTable,
    r11v: __m256i,
) {
    for g in 0..N {
        let av = soa_load_cell(a.add(32 * g));
        let bv = soa_load_cell(b.add(32 * g));
        let v = soa_ext_mul(&av, &bv, r11v);
        for l in 0..4 {
            let p = lazy.add(lazy_off(g, l));
            let mut acc = LazyLimb::load(p);
            acc.mla(table.m[l][0], v[0]);
            acc.mla(table.m[l][1], v[1]);
            acc.condsub();
            acc.mla(table.m[l][2], v[2]);
            acc.mla(table.m[l][3], v[3]);
            acc.condsub();
            acc.store(p);
        }
    }
}

/// `lazy[cell] += coeff (x) a[cell]` over the first N ext cell groups, lazily.
#[inline(always)]
pub(crate) unsafe fn soa_lin_ext_lazy<const N: usize>(
    lazy: *mut u64,
    a: *const u32,
    table: &SoaExtTable,
) {
    for g in 0..N {
        let v = soa_load_cell(a.add(32 * g));
        for l in 0..4 {
            let p = lazy.add(lazy_off(g, l));
            let mut acc = LazyLimb::load(p);
            acc.mla(table.m[l][0], v[0]);
            acc.mla(table.m[l][1], v[1]);
            acc.condsub();
            acc.mla(table.m[l][2], v[2]);
            acc.mla(table.m[l][3], v[3]);
            acc.condsub();
            acc.store(p);
        }
    }
}

// ---------------------------------------------------------------------------
// form (bracket) ops
// ---------------------------------------------------------------------------

#[inline(always)]
pub(crate) unsafe fn soa_base_form_add_n<const N: usize>(dst: *mut u32, src: *const u32) {
    for i in 0..N {
        let p = dst.add(8 * i);
        st(p, add8(ld(p), ld(src.add(8 * i))));
    }
}
#[inline(always)]
pub(crate) unsafe fn soa_base_form_store_n<const N: usize>(dst: *mut u32, src: *const u32) {
    for i in 0..N {
        st(dst.add(8 * i), ld(src.add(8 * i)));
    }
}
#[inline(always)]
pub(crate) unsafe fn soa_base_form_neg_store_n<const N: usize>(dst: *mut u32, src: *const u32) {
    let zero = _mm256_setzero_si256();
    for i in 0..N {
        st(dst.add(8 * i), sub8(zero, ld(src.add(8 * i))));
    }
}
#[inline(always)]
pub(crate) unsafe fn soa_base_form_mul_store_n<const N: usize>(
    dst: *mut u32,
    src: *const u32,
    c: BabyBearField,
) {
    let cv = bc32(c.raw_u32_value());
    for i in 0..N {
        st(dst.add(8 * i), mont_mul8(ld(src.add(8 * i)), cv));
    }
}
#[inline(always)]
pub(crate) unsafe fn soa_base_form_sub_n<const N: usize>(dst: *mut u32, src: *const u32) {
    for i in 0..N {
        let p = dst.add(8 * i);
        st(p, sub8(ld(p), ld(src.add(8 * i))));
    }
}
#[inline(always)]
pub(crate) unsafe fn soa_base_form_muladd_n<const N: usize>(
    dst: *mut u32,
    src: *const u32,
    c: BabyBearField,
) {
    let cv = bc32(c.raw_u32_value());
    for i in 0..N {
        let p = dst.add(8 * i);
        st(p, add8(ld(p), mont_mul8(ld(src.add(8 * i)), cv)));
    }
}
/// `dst[cell] += c` over the FIRST N base cell groups (real evaluation cells).
#[inline(always)]
pub(crate) unsafe fn soa_base_form_add_const_n<const N: usize>(dst: *mut u32, c: BabyBearField) {
    let cv = bc32(c.raw_u32_value());
    for i in 0..N {
        let p = dst.add(8 * i);
        st(p, add8(ld(p), cv));
    }
}

/// Ext-grid form ops over N cell groups (4N limb vectors).
#[inline(always)]
pub(crate) unsafe fn soa_ext_form_add_n<const N: usize>(dst: *mut u32, src: *const u32) {
    for i in 0..4 * N {
        let p = dst.add(8 * i);
        st(p, add8(ld(p), ld(src.add(8 * i))));
    }
}
#[inline(always)]
pub(crate) unsafe fn soa_ext_form_store_n<const N: usize>(dst: *mut u32, src: *const u32) {
    for i in 0..4 * N {
        st(dst.add(8 * i), ld(src.add(8 * i)));
    }
}
#[inline(always)]
pub(crate) unsafe fn soa_ext_form_neg_store_n<const N: usize>(dst: *mut u32, src: *const u32) {
    let zero = _mm256_setzero_si256();
    for i in 0..4 * N {
        st(dst.add(8 * i), sub8(zero, ld(src.add(8 * i))));
    }
}
#[inline(always)]
pub(crate) unsafe fn soa_ext_form_mul_store_n<const N: usize>(
    dst: *mut u32,
    src: *const u32,
    c: BabyBearField,
) {
    let cv = bc32(c.raw_u32_value());
    for i in 0..4 * N {
        st(dst.add(8 * i), mont_mul8(ld(src.add(8 * i)), cv));
    }
}
#[inline(always)]
pub(crate) unsafe fn soa_ext_form_sub_n<const N: usize>(dst: *mut u32, src: *const u32) {
    for i in 0..4 * N {
        let p = dst.add(8 * i);
        st(p, sub8(ld(p), ld(src.add(8 * i))));
    }
}
#[inline(always)]
pub(crate) unsafe fn soa_ext_form_muladd_n<const N: usize>(
    dst: *mut u32,
    src: *const u32,
    c: BabyBearField,
) {
    let cv = bc32(c.raw_u32_value());
    for i in 0..4 * N {
        let p = dst.add(8 * i);
        st(p, add8(ld(p), mont_mul8(ld(src.add(8 * i)), cv)));
    }
}
/// The base constant lands on limb 0 only, over the FIRST N ext cell groups.
#[inline(always)]
pub(crate) unsafe fn soa_ext_form_add_base_const_n<const N: usize>(
    dst: *mut u32,
    c: BabyBearField,
) {
    let cv = bc32(c.raw_u32_value());
    for g in 0..N {
        let p = dst.add(32 * g);
        st(p, add8(ld(p), cv));
    }
}

/// Limb-major SoA cell groups -> 8N contiguous AoS ext values.
#[inline(always)]
pub(crate) unsafe fn soa_untranspose_to_aos_ext<const N: usize>(
    acc: *const u32,
    out: *mut BabyBearExt4,
) {
    for g in 0..N {
        let l = soa_load_cell(acc.add(32 * g));
        soa_store_ext8(&l, out.add(8 * g));
    }
}

// ---------------------------------------------------------------------------
// LSB-layout 8-tap folds, 8 output rows per call
// ---------------------------------------------------------------------------

/// 8-tap fold of a base poly, 8 consecutive OUTPUT rows: the rows' 64
/// contiguous taps are transposed in-register into tap-column vectors
/// (lanes = rows), then lazy-accumulated against the broadcast ext weights.
/// Returns the limb-major SoA block of the 8 folded ext values.
#[inline(always)]
pub(crate) unsafe fn lsb_soa_fold8_base(
    src: *const BabyBearField,
    prefix_limbs: &[[__m256i; 4]; 8], // [tap][limb] broadcast
    blk: usize,                       // output rows 8*blk .. 8*blk+8
) -> [__m256i; 4] {
    let p = (src as *const u32).add(blk * 64);
    let rows: [__m256i; 8] = core::array::from_fn(|r| ld(p.add(8 * r)));
    let taps = transpose_8x8(&rows); // taps[i] = tap i over the 8 rows
    let mut acc = [LazyLimb::zero(); 4];
    for i in 0..8 {
        for j in 0..4 {
            acc[j].mla(prefix_limbs[i][j], taps[i]);
        }
        if i % 2 == 1 {
            for j in 0..4 {
                acc[j].condsub();
            }
        }
    }
    core::array::from_fn(|j| acc[j].redc())
}

/// 8-tap fold of an ext poly, 8 consecutive OUTPUT rows: per tap the 8 rows'
/// elements (stride 8) are transposed to limb-major and lazy-accumulated
/// through the tap's canonical [`SoaExtTable`].
#[inline(always)]
pub(crate) unsafe fn lsb_soa_fold8_ext(
    src: *const BabyBearExt4,
    tables: &[SoaExtTable; 8],
    blk: usize,
) -> [__m256i; 4] {
    let base = src.add(blk * 64);
    let mut acc = [LazyLimb::zero(); 4];
    for i in 0..8 {
        let v = soa_transpose_ext8_strided(base.add(i), 8);
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
