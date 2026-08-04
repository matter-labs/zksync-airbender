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
use ::field::PrimeField;

const P: u32 = 0x78000001;
const K: u32 = 0x77ffffff; // -P^{-1} mod 2^32 (matches BabyBearField::MONT_K)

#[inline(always)]
pub fn is_bb_pair<F: 'static, E: 'static>() -> bool {
    core::any::TypeId::of::<F>() == core::any::TypeId::of::<BabyBearField>()
        && core::any::TypeId::of::<E>() == core::any::TypeId::of::<BabyBearExt4>()
}

#[inline(always)]
pub fn is_bb4<E: 'static>() -> bool {
    core::any::TypeId::of::<E>() == core::any::TypeId::of::<BabyBearExt4>()
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
/// base poly (ext-by-base per tap).
#[inline(always)]
pub unsafe fn fold8_base(
    src: *const BabyBearField,
    prefix: &[BabyBearExt4; 8],
    stride: usize,
    row: usize,
) -> BabyBearExt4 {
    let pv = prefix.as_ptr();
    let mut offset = row;
    let mut acc = mont_mul4(
        load_e(pv),
        vdupq_n_u32((*src.add(offset)).raw_u32_value()),
    );
    offset += stride;
    for i in 1..8 {
        let t = mont_mul4(
            load_e(pv.add(i)),
            vdupq_n_u32((*src.add(offset)).raw_u32_value()),
        );
        acc = add4(acc, t);
        offset += stride;
    }
    core::mem::transmute(acc)
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
    let mut offset = row;
    let mut acc = ext_mul_var(load_e(pv), load_e(src.add(offset)), r11v);
    offset += stride;
    for i in 1..8 {
        let t = ext_mul_var(load_e(pv.add(i)), load_e(src.add(offset)), r11v);
        acc = add4(acc, t);
        offset += stride;
    }
    core::mem::transmute(acc)
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
pub unsafe fn linear_ext_27(
    dst: *mut BabyBearExt4,
    a: *const BabyBearExt4,
    coeff: &BabyBearExt4,
) {
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
            let got2: BabyBearExt4 =
                unsafe { core::mem::transmute(mat_mul(&m, load_e(&a))) };
            assert_eq!(got2, expected);
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
