//! AVX-512 SoA chunk kernels of the dimension-reducing backward path
//! (BabyBear/Ext4), the 16-lane replacement of the AVX2 `avx2_initial_chunk`
//! / `avx2_continuing_chunk` pair with the same contracts and byte-identical
//! results.
//!
//! The dimension-reducing gate set is fixed (pairwise products and logup
//! fraction adds), so the kernels are specialized end to end:
//! * 16 rows at a time: a row's 4 (initial) or 8 (continuing) AoS `Ext4`
//!   values are 1 or 2 vectors, one 16x16 transpose turns 16 rows into
//!   limb-major streams (16 lanes = 16 rows), the folded values go back
//!   through the inverse transpose and are stored once;
//! * the fold-on-read (`lo + r (hi - lo)`), the gate products at `X = 0`
//!   and `X = inf` and the `T`-weighted accumulation all use LAZY
//!   arithmetic (raw `u64` cross products, one REDC per limb) — no
//!   canonical `Ext4` multiply anywhere in the row loop;
//! * the batching by `alpha` is factored OUT of the row loop (Horner over
//!   the relations): each relation accumulates `sum_j T_j (x) v_j` for its
//!   two components over the whole chunk, and `alpha` multiplies the two
//!   reduced sums once per chunk. Field arithmetic is exact, so the result
//!   equals the per-row batched form the AVX2 kernel computes.
//! Rows beyond the last multiple of 16 of a chunk run through the AVX2
//! kernel (its tri scratch is only used for that tail).

use std::collections::BTreeMap;

use super::super::dimension_reduction::lsb_backward::{FoldBufferTracker, LsbDimReducingRelation};
use super::super::{GKRAddress, SendConstPtr};
use super::avx2::{avx2_continuing_chunk, avx2_initial_chunk};
use crate::gkr::prover::sumcheck_loop::windowed_mode::avx512 as k;
use crate::gkr::prover::sumcheck_loop::windowed_mode::avx512::{
    ExtPerm, ExtTable16, Lazy16, LazyRhs,
};
use ::field::baby_bear::ext4::BabyBearExt4;
use core::arch::x86_64::*;
use field::Field;

type Limbs = [__m512i; 4];

#[inline(always)]
fn as_bb<E: Field>(c: &E) -> &BabyBearExt4 {
    unsafe { &*(c as *const E as *const _) }
}

#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn hi4(v: &Limbs) -> Limbs {
    core::array::from_fn(|l| k::hi64(v[l]))
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn sub4(a: &Limbs, b: &Limbs) -> Limbs {
    core::array::from_fn(|l| k::sub16(a[l], b[l]))
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn add4(a: &Limbs, b: &Limbs) -> Limbs {
    core::array::from_fn(|l| k::add16(a[l], b[l]))
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn zero4() -> [Lazy16; 4] {
    [Lazy16::zero(); 4]
}

/// 16 rows (`row_stride` u32 each, one vector = 4 AoS ext values per row
/// read at `base + row * row_stride`) -> 16 column vectors: `4 s + l` =
/// limb `l` of the row's `s`-th element over the 16 rows.
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn load_rows16(base: *const u32, row_stride: usize, j0: usize) -> [__m512i; 16] {
    let r: [__m512i; 16] = core::array::from_fn(|jj| k::ld(base.add((j0 + jj) * row_stride)));
    k::transpose16(&r)
}
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn stream(t: &[__m512i; 16], s: usize) -> Limbs {
    [t[4 * s], t[4 * s + 1], t[4 * s + 2], t[4 * s + 3]]
}

/// The output layer's `X = 0` gate values of rows `j0 .. j0 + 16`
/// (`out[2 j]`): the even elements of 32 consecutive ones, limb-major.
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn load_even16(
    out: *const BabyBearExt4,
    j0: usize,
    xp: &ExtPerm,
    even_idx: __m512i,
) -> Limbs {
    let za: [__m512i; 4] =
        core::array::from_fn(|i| _mm512_loadu_si512(out.add(2 * j0 + 4 * i) as *const __m512i));
    let zb: [__m512i; 4] =
        core::array::from_fn(
            |i| _mm512_loadu_si512(out.add(2 * j0 + 16 + 4 * i) as *const __m512i),
        );
    let la = k::transpose_ext16_vecs(&za, xp);
    let lb = k::transpose_ext16_vecs(&zb, xp);
    core::array::from_fn(|l| _mm512_permutex2var_epi32(la[l], even_idx, lb[l]))
}

/// The eq weights `T[j0 .. j0 + 16]` as a prepared lazy right operand.
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn load_t16(t_tab: *const BabyBearExt4, j0: usize, xp: &ExtPerm, r11: __m512i) -> LazyRhs {
    let z: [__m512i; 4] =
        core::array::from_fn(|i| _mm512_loadu_si512(t_tab.add(j0 + 4 * i) as *const __m512i));
    LazyRhs::new(&k::transpose_ext16_vecs(&z, xp), r11)
}

/// A lazy accumulator's chunk total: REDC per limb, modular sum over lanes.
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn reduce_acc(acc: &[Lazy16; 4]) -> BabyBearExt4 {
    let limbs: [u32; 4] = core::array::from_fn(|l| k::hsum_mod(acc[l].redc()));
    core::mem::transmute(limbs)
}

#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn acc_weighted(acc: &mut [Lazy16; 4], v: &Limbs, tw: &LazyRhs) {
    k::lazy_mul_acc(acc, v, &hi4(v), tw);
}

/// Fold-on-read of one tracker's 16 rows: row `j` holds 8 elements
/// `[v0_lo, v1_lo, v0_hi, v1_hi, v2_lo, v3_lo, v2_hi, v3_hi]`; the folded
/// `[v0, v1, v2, v3]` (`lo + r (hi - lo)`) are stored to the output row
/// (4 elements) and returned limb-major.
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn fold_rows16(
    src: *const u32,
    dst: *mut u32,
    j0: usize,
    table_r: &ExtTable16,
) -> [Limbs; 4] {
    let ta = load_rows16(src, 32, j0);
    let tb = load_rows16(src.add(16), 32, j0);
    let fold = |lo: Limbs, hi: Limbs| -> Limbs {
        let d = sub4(&hi, &lo);
        add4(&lo, &table_r.mul(&d, &hi4(&d)))
    };
    let v = [
        fold(stream(&ta, 0), stream(&ta, 2)),
        fold(stream(&ta, 1), stream(&ta, 3)),
        fold(stream(&tb, 0), stream(&tb, 2)),
        fold(stream(&tb, 1), stream(&tb, 3)),
    ];
    let cols: [__m512i; 16] = core::array::from_fn(|c| v[c / 4][c % 4]);
    let rows = k::transpose16(&cols);
    for jj in 0..16 {
        k::st(dst.add((j0 + jj) * 16), rows[jj]);
    }
    v
}

const EVEN_IDX: [i32; 16] = [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30];

/// INITIAL round over `rows` (a multiple of 16) rows from `chunk_start`.
#[target_feature(enable = "avx512f")]
unsafe fn initial_blocks<E: Field>(
    inputs: &BTreeMap<GKRAddress, &[E]>,
    outputs: &BTreeMap<GKRAddress, &[E]>,
    relations: &[LsbDimReducingRelation<E>],
    t_ptr: SendConstPtr<E>,
    chunk_start: usize,
    rows: usize,
) -> [BabyBearExt4; 2] {
    let r11 = k::r11v();
    let xp = ExtPerm::new();
    let even_idx = k::idx(&EVEN_IDX);
    let t_tab = t_ptr.0 as *const BabyBearExt4;
    let mut total = [BabyBearExt4::ZERO; 2];
    for rel in relations.iter() {
        match rel {
            LsbDimReducingRelation::PairwiseProduct {
                input,
                output,
                alpha,
            } => {
                let src = inputs[input].as_ptr() as *const u32;
                let out = outputs[output].as_ptr() as *const BabyBearExt4;
                let (mut s0, mut sinf) = (zero4(), zero4());
                let mut j = chunk_start;
                while j < chunk_start + rows {
                    let t = load_rows16(src, 16, j);
                    let (a0, b0, a1, b1) =
                        (stream(&t, 0), stream(&t, 1), stream(&t, 2), stream(&t, 3));
                    let pinf = k::soa_ext_mul_lazy(&sub4(&a1, &a0), &sub4(&b1, &b0), r11);
                    let v0 = load_even16(out, j, &xp, even_idx);
                    let tw = load_t16(t_tab, j, &xp, r11);
                    acc_weighted(&mut s0, &v0, &tw);
                    acc_weighted(&mut sinf, &pinf, &tw);
                    j += 16;
                }
                let alpha = as_bb(alpha);
                let mut e0 = reduce_acc(&s0);
                e0.mul_assign(alpha);
                total[0].add_assign(&e0);
                let mut ei = reduce_acc(&sinf);
                ei.mul_assign(alpha);
                total[1].add_assign(&ei);
            }
            LsbDimReducingRelation::LogupPair {
                num,
                den,
                num_output,
                den_output,
                alpha_num,
                alpha_den,
            } => {
                let n_src = inputs[num].as_ptr() as *const u32;
                let d_src = inputs[den].as_ptr() as *const u32;
                let n_out = outputs[num_output].as_ptr() as *const BabyBearExt4;
                let d_out = outputs[den_output].as_ptr() as *const BabyBearExt4;
                let (mut sn0, mut sni, mut sd0, mut sdi) = (zero4(), zero4(), zero4(), zero4());
                let mut j = chunk_start;
                while j < chunk_start + rows {
                    let tn = load_rows16(n_src, 16, j);
                    let td = load_rows16(d_src, 16, j);
                    let (n0, n1, n2, n3) = (
                        stream(&tn, 0),
                        stream(&tn, 1),
                        stream(&tn, 2),
                        stream(&tn, 3),
                    );
                    let (d0, d1, d2, d3) = (
                        stream(&td, 0),
                        stream(&td, 1),
                        stream(&td, 2),
                        stream(&td, 3),
                    );
                    let (dn0, dn1) = (sub4(&n2, &n0), sub4(&n3, &n1));
                    let (dd0, dd1) = (sub4(&d2, &d0), sub4(&d3, &d1));
                    let numi = add4(
                        &k::soa_ext_mul_lazy(&dn0, &dd1, r11),
                        &k::soa_ext_mul_lazy(&dn1, &dd0, r11),
                    );
                    let deni = k::soa_ext_mul_lazy(&dd0, &dd1, r11);
                    let num0 = load_even16(n_out, j, &xp, even_idx);
                    let den0 = load_even16(d_out, j, &xp, even_idx);
                    let tw = load_t16(t_tab, j, &xp, r11);
                    acc_weighted(&mut sn0, &num0, &tw);
                    acc_weighted(&mut sni, &numi, &tw);
                    acc_weighted(&mut sd0, &den0, &tw);
                    acc_weighted(&mut sdi, &deni, &tw);
                    j += 16;
                }
                let (an, ad) = (as_bb(alpha_num), as_bb(alpha_den));
                for (acc, alpha, slot) in [
                    (&sn0, an, 0usize),
                    (&sni, an, 1),
                    (&sd0, ad, 0),
                    (&sdi, ad, 1),
                ] {
                    let mut e = reduce_acc(acc);
                    e.mul_assign(alpha);
                    total[slot].add_assign(&e);
                }
            }
        }
    }
    total
}

/// CONTINUING round over `rows` (a multiple of 16) rows from `chunk_start`.
#[target_feature(enable = "avx512f")]
unsafe fn continuing_blocks<E: Field>(
    buffers: &BTreeMap<GKRAddress, FoldBufferTracker<E>>,
    relations: &[LsbDimReducingRelation<E>],
    folding_challenge: &BabyBearExt4,
    t_ptr: SendConstPtr<E>,
    chunk_start: usize,
    rows: usize,
) -> [BabyBearExt4; 2] {
    let r11 = k::r11v();
    let xp = ExtPerm::new();
    let table_r = ExtTable16::new(folding_challenge);
    let t_tab = t_ptr.0 as *const BabyBearExt4;
    let mut total = [BabyBearExt4::ZERO; 2];
    for rel in relations.iter() {
        match rel {
            LsbDimReducingRelation::PairwiseProduct { input, alpha, .. } => {
                let src = buffers[input].input_ptr_range().start as *const u32;
                let dst = buffers[input].output_ptr_range().start as *mut u32;
                let (mut s0, mut sinf) = (zero4(), zero4());
                let mut j = chunk_start;
                while j < chunk_start + rows {
                    let [a0, b0, a1, b1] = fold_rows16(src, dst, j, &table_r);
                    let p0 = k::soa_ext_mul_lazy(&a0, &b0, r11);
                    let pinf = k::soa_ext_mul_lazy(&sub4(&a1, &a0), &sub4(&b1, &b0), r11);
                    let tw = load_t16(t_tab, j, &xp, r11);
                    acc_weighted(&mut s0, &p0, &tw);
                    acc_weighted(&mut sinf, &pinf, &tw);
                    j += 16;
                }
                let alpha = as_bb(alpha);
                let mut e0 = reduce_acc(&s0);
                e0.mul_assign(alpha);
                total[0].add_assign(&e0);
                let mut ei = reduce_acc(&sinf);
                ei.mul_assign(alpha);
                total[1].add_assign(&ei);
            }
            LsbDimReducingRelation::LogupPair {
                num,
                den,
                alpha_num,
                alpha_den,
                ..
            } => {
                let n_src = buffers[num].input_ptr_range().start as *const u32;
                let n_dst = buffers[num].output_ptr_range().start as *mut u32;
                let d_src = buffers[den].input_ptr_range().start as *const u32;
                let d_dst = buffers[den].output_ptr_range().start as *mut u32;
                let (mut sn0, mut sni, mut sd0, mut sdi) = (zero4(), zero4(), zero4(), zero4());
                let mut j = chunk_start;
                while j < chunk_start + rows {
                    let [n0, n1, n2, n3] = fold_rows16(n_src, n_dst, j, &table_r);
                    let [d0, d1, d2, d3] = fold_rows16(d_src, d_dst, j, &table_r);
                    let num0 = add4(
                        &k::soa_ext_mul_lazy(&n0, &d1, r11),
                        &k::soa_ext_mul_lazy(&n1, &d0, r11),
                    );
                    let den0 = k::soa_ext_mul_lazy(&d0, &d1, r11);
                    let (dn0, dn1) = (sub4(&n2, &n0), sub4(&n3, &n1));
                    let (dd0, dd1) = (sub4(&d2, &d0), sub4(&d3, &d1));
                    let numi = add4(
                        &k::soa_ext_mul_lazy(&dn0, &dd1, r11),
                        &k::soa_ext_mul_lazy(&dn1, &dd0, r11),
                    );
                    let deni = k::soa_ext_mul_lazy(&dd0, &dd1, r11);
                    let tw = load_t16(t_tab, j, &xp, r11);
                    acc_weighted(&mut sn0, &num0, &tw);
                    acc_weighted(&mut sni, &numi, &tw);
                    acc_weighted(&mut sd0, &den0, &tw);
                    acc_weighted(&mut sdi, &deni, &tw);
                    j += 16;
                }
                let (an, ad) = (as_bb(alpha_num), as_bb(alpha_den));
                for (acc, alpha, slot) in [
                    (&sn0, an, 0usize),
                    (&sni, an, 1),
                    (&sd0, ad, 0),
                    (&sdi, ad, 1),
                ] {
                    let mut e = reduce_acc(acc);
                    e.mul_assign(alpha);
                    total[slot].add_assign(&e);
                }
            }
        }
    }
    total
}

#[inline(always)]
fn to_e<E: Field>(v: [BabyBearExt4; 2]) -> [E; 2] {
    unsafe { [*(v.as_ptr() as *const E), *(v.as_ptr().add(1) as *const E)] }
}

/// AVX-512 chunk kernel of the INITIAL round (contract of
/// `avx2_initial_chunk`; `E` must be BabyBearExt4).
///
/// # Safety
///
/// Same pointer contract as `scalar_initial_chunk`; `scratch` must hold
/// `chunk_size` 32-byte slots (used for the tail rows only).
pub unsafe fn avx512_initial_chunk<E: Field>(
    inputs: &BTreeMap<GKRAddress, &[E]>,
    outputs: &BTreeMap<GKRAddress, &[E]>,
    relations: &[LsbDimReducingRelation<E>],
    t_ptr: SendConstPtr<E>,
    chunk_start: usize,
    chunk_size: usize,
    scratch: crate::gkr::prover::SendPtr<[u128; 2]>,
) -> [E; 2] {
    let full = chunk_size & !15;
    let mut acc = [E::ZERO; 2];
    if full > 0 {
        let r = initial_blocks(inputs, outputs, relations, t_ptr, chunk_start, full);
        acc = to_e(r);
    }
    if full < chunk_size {
        let t = avx2_initial_chunk(
            inputs,
            outputs,
            relations,
            t_ptr,
            chunk_start + full,
            chunk_size - full,
            scratch,
        );
        acc[0].add_assign(&t[0]);
        acc[1].add_assign(&t[1]);
    }
    acc
}

/// AVX-512 chunk kernel of a CONTINUING round (contract of
/// `avx2_continuing_chunk`; `E` must be BabyBearExt4).
///
/// # Safety
///
/// Same pointer contract as `scalar_continuing_chunk`; `scratch` must hold
/// `chunk_size` 32-byte slots (used for the tail rows only).
pub unsafe fn avx512_continuing_chunk<E: Field>(
    buffers: &BTreeMap<GKRAddress, FoldBufferTracker<E>>,
    relations: &[LsbDimReducingRelation<E>],
    folding_challenge: E,
    t_ptr: SendConstPtr<E>,
    chunk_start: usize,
    chunk_size: usize,
    scratch: crate::gkr::prover::SendPtr<[u128; 2]>,
) -> [E; 2] {
    let full = chunk_size & !15;
    let mut acc = [E::ZERO; 2];
    if full > 0 {
        let r = continuing_blocks(
            buffers,
            relations,
            as_bb(&folding_challenge),
            t_ptr,
            chunk_start,
            full,
        );
        acc = to_e(r);
    }
    if full < chunk_size {
        let t = avx2_continuing_chunk(
            buffers,
            relations,
            folding_challenge,
            t_ptr,
            chunk_start + full,
            chunk_size - full,
            scratch,
        );
        acc[0].add_assign(&t[0]);
        acc[1].add_assign(&t[1]);
    }
    acc
}

// ---------------------------------------------------------------------------
// forward (output-construction) ops of the dimension-reducing layers
// ---------------------------------------------------------------------------

/// Outputs below this count are produced by a plain serial loop: the later
/// dimension-reducing stages are tiny and the pool scope + vector setup
/// costs more than the work.
pub const FORWARD_VECTOR_MIN: usize = 1 << 12;

const ODD_IDX: [i32; 16] = [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31];

/// The even and odd elements of 32 consecutive AoS ext values, limb-major.
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn load_even_odd16(
    src: *const BabyBearExt4,
    xp: &ExtPerm,
    even_idx: __m512i,
    odd_idx: __m512i,
) -> (Limbs, Limbs) {
    let za: [__m512i; 4] =
        core::array::from_fn(|i| _mm512_loadu_si512(src.add(4 * i) as *const __m512i));
    let zb: [__m512i; 4] =
        core::array::from_fn(|i| _mm512_loadu_si512(src.add(16 + 4 * i) as *const __m512i));
    let la = k::transpose_ext16_vecs(&za, xp);
    let lb = k::transpose_ext16_vecs(&zb, xp);
    (
        core::array::from_fn(|l| _mm512_permutex2var_epi32(la[l], even_idx, lb[l])),
        core::array::from_fn(|l| _mm512_permutex2var_epi32(la[l], odd_idx, lb[l])),
    )
}

/// `out[i] = in[2i] (x) in[2i+1]` for outputs `range` (a multiple of 16
/// wide, 16-aligned).
#[target_feature(enable = "avx512f")]
unsafe fn pairwise_blocks(
    src: *const BabyBearExt4,
    dst: *mut BabyBearExt4,
    range: core::ops::Range<usize>,
) {
    let r11 = k::r11v();
    let xp = ExtPerm::new();
    let (ei, oi) = (k::idx(&EVEN_IDX), k::idx(&ODD_IDX));
    let nt = k::nt_stores();
    let mut i = range.start;
    while i < range.end {
        let (a, b) = load_even_odd16(src.add(2 * i), &xp, ei, oi);
        k::store_ext16_out(&k::soa_ext_mul_lazy(&a, &b, r11), dst.add(i), &xp, nt);
        i += 16;
    }
    _mm_sfence();
}

/// `num[i] = n[2i] d[2i+1] + n[2i+1] d[2i]`, `den[i] = d[2i] d[2i+1]`.
#[target_feature(enable = "avx512f")]
unsafe fn logup_blocks(
    n_src: *const BabyBearExt4,
    d_src: *const BabyBearExt4,
    n_dst: *mut BabyBearExt4,
    d_dst: *mut BabyBearExt4,
    range: core::ops::Range<usize>,
) {
    let r11 = k::r11v();
    let xp = ExtPerm::new();
    let (ei, oi) = (k::idx(&EVEN_IDX), k::idx(&ODD_IDX));
    let nt = k::nt_stores();
    let mut i = range.start;
    while i < range.end {
        let (n0, n1) = load_even_odd16(n_src.add(2 * i), &xp, ei, oi);
        let (d0, d1) = load_even_odd16(d_src.add(2 * i), &xp, ei, oi);
        let num = add4(
            &k::soa_ext_mul_lazy(&n0, &d1, r11),
            &k::soa_ext_mul_lazy(&n1, &d0, r11),
        );
        k::store_ext16_out(&num, n_dst.add(i), &xp, nt);
        k::store_ext16_out(&k::soa_ext_mul_lazy(&d0, &d1, r11), d_dst.add(i), &xp, nt);
        i += 16;
    }
    _mm_sfence();
}

/// Forward pairwise product with AVX-512 SoA blocks over the worker for
/// large outputs and a serial scalar loop below [`FORWARD_VECTOR_MIN`];
/// `use_avx512 == false` falls back to the AVX2 op. Pooled output buffer.
pub fn forward_pairwise_x86<F: field::PrimeField, E: field::FieldExtension<F> + Field>(
    gkr_storage: &mut crate::gkr::prover::GKRStorage<F, E>,
    input: GKRAddress,
    output: GKRAddress,
    expected_output_layer: usize,
    input_trace_len: usize,
    pool: &dyn crate::allocation_pool::AllocationPool<F, E>,
    worker: &worker::Worker,
    use_avx512: bool,
) {
    use crate::gkr::sumcheck::evaluation_kernels::GKRInputs;
    use crate::gkr::PAR_THRESHOLD;
    let output_trace_len = input_trace_len / 2;
    if !use_avx512 {
        return super::avx2::forward_pairwise_avx2(
            gkr_storage,
            input,
            output,
            expected_output_layer,
            input_trace_len,
            pool,
            worker,
        );
    }
    unsafe {
        let inputs = GKRInputs {
            inputs_in_base: Vec::new(),
            inputs_in_extension: vec![input],
            outputs_in_base: Vec::new(),
            outputs_in_extension: Vec::new(),
        };
        let sources = gkr_storage.get_for_sumcheck_round_0(&inputs);
        let src: &[E] = sources.extension_field_inputs[0].current_values();
        let mut destination = pool.alloc_ext(
            output_trace_len,
            crate::allocation_pool::ColumnLayout::Contiguous,
        );
        if output_trace_len < FORWARD_VECTOR_MIN {
            for i in 0..output_trace_len {
                let mut v = src[2 * i];
                v.mul_assign(&src[2 * i + 1]);
                destination.as_mut()[i].write(v);
            }
        } else {
            assert_eq!(output_trace_len % 16, 0);
            let blocks = output_trace_len / 16;
            let src_addr = SendConstPtr(src.as_ptr());
            let dst_addr = crate::gkr::prover::SendPtr(destination.as_mut_ptr());
            worker.scope_with_threshold(blocks, (PAR_THRESHOLD / 16).max(1), |scope, geometry| {
                for thread_idx in 0..geometry.num_chunks {
                    let start = geometry.get_chunk_start_pos(thread_idx) * 16;
                    let size = geometry.get_chunk_size(thread_idx) * 16;
                    worker::Worker::smart_spawn(
                        scope,
                        thread_idx == geometry.len() - 1,
                        move |_| {
                            pairwise_blocks(
                                src_addr.get() as *const BabyBearExt4,
                                dst_addr.get() as *mut BabyBearExt4,
                                start..start + size,
                            );
                        },
                    )
                }
            });
        }
        output.assert_as_layer(expected_output_layer);
        gkr_storage.insert_extension_at_layer(
            expected_output_layer,
            output,
            crate::gkr::sumcheck::access_and_fold::ExtensionFieldPoly::from_pooled(destination),
        );
    }
}

/// Forward logup fraction add, same dispatch as [`forward_pairwise_x86`].
pub fn forward_logup_x86<F: field::PrimeField, E: field::FieldExtension<F> + Field>(
    gkr_storage: &mut crate::gkr::prover::GKRStorage<F, E>,
    inputs: [GKRAddress; 2],
    outputs: [GKRAddress; 2],
    expected_output_layer: usize,
    input_trace_len: usize,
    pool: &dyn crate::allocation_pool::AllocationPool<F, E>,
    worker: &worker::Worker,
    use_avx512: bool,
) {
    use crate::gkr::sumcheck::evaluation_kernels::GKRInputs;
    use crate::gkr::PAR_THRESHOLD;
    let output_trace_len = input_trace_len / 2;
    if !use_avx512 {
        return super::avx2::forward_logup_avx2(
            gkr_storage,
            inputs,
            outputs,
            expected_output_layer,
            input_trace_len,
            pool,
            worker,
        );
    }
    unsafe {
        let gkr_inputs = GKRInputs {
            inputs_in_base: Vec::new(),
            inputs_in_extension: inputs.to_vec(),
            outputs_in_base: Vec::new(),
            outputs_in_extension: Vec::new(),
        };
        let sources = gkr_storage.get_for_sumcheck_round_0(&gkr_inputs);
        let n_src: &[E] = sources.extension_field_inputs[0].current_values();
        let d_src: &[E] = sources.extension_field_inputs[1].current_values();
        let mut num_dst = pool.alloc_ext(
            output_trace_len,
            crate::allocation_pool::ColumnLayout::Contiguous,
        );
        let mut den_dst = pool.alloc_ext(
            output_trace_len,
            crate::allocation_pool::ColumnLayout::Contiguous,
        );
        if output_trace_len < FORWARD_VECTOR_MIN {
            for i in 0..output_trace_len {
                let (n0, n1, d0, d1) = (
                    n_src[2 * i],
                    n_src[2 * i + 1],
                    d_src[2 * i],
                    d_src[2 * i + 1],
                );
                let mut num = n0;
                num.mul_assign(&d1);
                let mut t = n1;
                t.mul_assign(&d0);
                num.add_assign(&t);
                let mut den = d0;
                den.mul_assign(&d1);
                num_dst.as_mut()[i].write(num);
                den_dst.as_mut()[i].write(den);
            }
        } else {
            assert_eq!(output_trace_len % 16, 0);
            let blocks = output_trace_len / 16;
            let n_addr = SendConstPtr(n_src.as_ptr());
            let d_addr = SendConstPtr(d_src.as_ptr());
            let nd_addr = crate::gkr::prover::SendPtr(num_dst.as_mut_ptr());
            let dd_addr = crate::gkr::prover::SendPtr(den_dst.as_mut_ptr());
            worker.scope_with_threshold(blocks, (PAR_THRESHOLD / 16).max(1), |scope, geometry| {
                for thread_idx in 0..geometry.num_chunks {
                    let start = geometry.get_chunk_start_pos(thread_idx) * 16;
                    let size = geometry.get_chunk_size(thread_idx) * 16;
                    worker::Worker::smart_spawn(
                        scope,
                        thread_idx == geometry.len() - 1,
                        move |_| {
                            logup_blocks(
                                n_addr.get() as *const BabyBearExt4,
                                d_addr.get() as *const BabyBearExt4,
                                nd_addr.get() as *mut BabyBearExt4,
                                dd_addr.get() as *mut BabyBearExt4,
                                start..start + size,
                            );
                        },
                    )
                }
            });
        }
        for (addr, dst) in outputs.into_iter().zip([num_dst, den_dst].into_iter()) {
            addr.assert_as_layer(expected_output_layer);
            gkr_storage.insert_extension_at_layer(
                expected_output_layer,
                addr,
                crate::gkr::sumcheck::access_and_fold::ExtensionFieldPoly::from_pooled(dst),
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gkr::prover::SendPtr;
    use ::field::baby_bear::base::BabyBearField;
    use ::field::{FieldExtension, PrimeField};

    type E = BabyBearExt4;

    fn pseudo_base(seed: &mut u64) -> BabyBearField {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        BabyBearField::from_u32_with_reduction((*seed >> 33) as u32)
    }
    fn pseudo_ext(seed: &mut u64) -> E {
        E::from_array_of_base(core::array::from_fn(|_| pseudo_base(seed)))
    }
    fn vec_e(n: usize, seed: &mut u64) -> Vec<E> {
        (0..n).map(|_| pseudo_ext(seed)).collect()
    }
    fn addr(i: usize) -> GKRAddress {
        GKRAddress::InnerLayer {
            layer: 3,
            offset: i,
        }
    }

    #[test]
    fn avx512_dr_chunks_match_avx2() {
        if !is_x86_feature_detected!("avx512f") {
            eprintln!("avx512f not available: skipping");
            return;
        }
        let mut seed = 5u64;
        // rows not a multiple of 16: the tail runs through the AVX2 kernel
        let rows = 16 * 5 + 7;
        let relations = vec![
            LsbDimReducingRelation::PairwiseProduct {
                input: addr(0),
                output: addr(10),
                alpha: pseudo_ext(&mut seed),
            },
            LsbDimReducingRelation::LogupPair {
                num: addr(1),
                den: addr(2),
                num_output: addr(11),
                den_output: addr(12),
                alpha_num: pseudo_ext(&mut seed),
                alpha_den: pseudo_ext(&mut seed),
            },
        ];
        let t: Vec<E> = vec_e(rows, &mut seed);
        let mut scratch: Vec<[u128; 2]> = vec![[0; 2]; rows];
        let sp = SendPtr(scratch.as_mut_ptr());
        let tp = SendConstPtr(t.as_ptr());

        // ---- initial round: 4 inputs per row, X = 0 from the output layer
        let ins: Vec<Vec<E>> = (0..3).map(|_| vec_e(4 * rows, &mut seed)).collect();
        let outs: Vec<Vec<E>> = (0..3).map(|_| vec_e(2 * rows, &mut seed)).collect();
        let mut inputs: BTreeMap<GKRAddress, &[E]> = BTreeMap::new();
        let mut outputs: BTreeMap<GKRAddress, &[E]> = BTreeMap::new();
        for i in 0..3 {
            inputs.insert(addr(i), &ins[i][..]);
            outputs.insert(addr(10 + i), &outs[i][..]);
        }
        let want =
            unsafe { avx2_initial_chunk::<E>(&inputs, &outputs, &relations, tp, 0, rows, sp) };
        let got =
            unsafe { avx512_initial_chunk::<E>(&inputs, &outputs, &relations, tp, 0, rows, sp) };
        assert_eq!(got, want, "initial round");
        // a sub-range starting inside the chunk
        let want =
            unsafe { avx2_initial_chunk::<E>(&inputs, &outputs, &relations, tp, 3, rows - 3, sp) };
        let got = unsafe {
            avx512_initial_chunk::<E>(&inputs, &outputs, &relations, tp, 3, rows - 3, sp)
        };
        assert_eq!(got, want, "initial round, offset");

        // ---- continuing round: 8 inputs per row folded to 4
        let r = pseudo_ext(&mut seed);
        let origs: Vec<Vec<E>> = (0..3).map(|_| vec_e(8 * rows, &mut seed)).collect();
        let mut pools_a: Vec<Vec<E>> = (0..3).map(|_| vec![E::ZERO; 6 * rows]).collect();
        let mut pools_b: Vec<Vec<E>> = (0..3).map(|_| vec![E::ZERO; 6 * rows]).collect();
        let mut make = |pools: &mut Vec<Vec<E>>| -> BTreeMap<GKRAddress, FoldBufferTracker<E>> {
            let mut m = BTreeMap::new();
            for i in 0..3 {
                let mut tr = FoldBufferTracker::new_with_first_output(
                    pools[i].as_mut_ptr(),
                    pools[i].len(),
                    4 * rows,
                );
                tr.set_external_input(&origs[i]);
                m.insert(addr(i), tr);
            }
            m
        };
        let bufs_a = make(&mut pools_a);
        let bufs_b = make(&mut pools_b);
        let want = unsafe { avx2_continuing_chunk::<E>(&bufs_a, &relations, r, tp, 0, rows, sp) };
        let got = unsafe { avx512_continuing_chunk::<E>(&bufs_b, &relations, r, tp, 0, rows, sp) };
        assert_eq!(got, want, "continuing round");
        for i in 0..3 {
            assert_eq!(
                &pools_a[i][..4 * rows],
                &pools_b[i][..4 * rows],
                "folded values of poly {i}"
            );
        }
    }

    #[test]
    fn avx512_forward_ops_match_avx2() {
        if !is_x86_feature_detected!("avx512f") {
            eprintln!("avx512f not available: skipping");
            return;
        }
        use crate::gkr::prover::GKRStorage;
        use crate::gkr::sumcheck::access_and_fold::ExtensionFieldPoly;
        let worker = worker::Worker::new_with_num_threads(3);
        let mut seed = 9u64;
        // 2^14 inputs (vector path) and 2^9 inputs (serial path)
        for log_in in [14usize, 9] {
            let n_in = 1usize << log_in;
            let mut storage = GKRStorage::<BabyBearField, E>::default();
            let layer = 2usize;
            for off in 0..3 {
                storage.insert_extension_at_layer(
                    layer,
                    GKRAddress::InnerLayer { layer, offset: off },
                    ExtensionFieldPoly::new(vec_e(n_in, &mut seed).into_boxed_slice()),
                );
            }
            let a = |off| GKRAddress::InnerLayer { layer, offset: off };
            let o = |off| GKRAddress::InnerLayer {
                layer: layer + 1,
                offset: off,
            };
            super::super::avx2::forward_pairwise_avx2(
                &mut storage,
                a(0),
                o(0),
                layer + 1,
                n_in,
                &crate::allocation_pool::GenericAllocationPool::proxy(),
                &worker,
            );
            forward_pairwise_x86(
                &mut storage,
                a(0),
                o(1),
                layer + 1,
                n_in,
                &crate::allocation_pool::GenericAllocationPool::proxy(),
                &worker,
                true,
            );
            assert_eq!(
                storage.try_get_ext_poly(o(0)),
                storage.try_get_ext_poly(o(1)),
                "pairwise {log_in}"
            );
            super::super::avx2::forward_logup_avx2(
                &mut storage,
                [a(1), a(2)],
                [o(2), o(3)],
                layer + 1,
                n_in,
                &crate::allocation_pool::GenericAllocationPool::proxy(),
                &worker,
            );
            forward_logup_x86(
                &mut storage,
                [a(1), a(2)],
                [o(4), o(5)],
                layer + 1,
                n_in,
                &crate::allocation_pool::GenericAllocationPool::proxy(),
                &worker,
                true,
            );
            assert_eq!(
                storage.try_get_ext_poly(o(2)),
                storage.try_get_ext_poly(o(4)),
                "logup num {log_in}"
            );
            assert_eq!(
                storage.try_get_ext_poly(o(3)),
                storage.try_get_ext_poly(o(5)),
                "logup den {log_in}"
            );
        }
    }
}
