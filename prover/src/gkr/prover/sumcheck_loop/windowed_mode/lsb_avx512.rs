//! AVX-512 twin of [`super::lsb_avx2`]: the SoA window-3 passes (initial
//! over the layer's base/ext columns, continuing over the folded ext tables)
//! and the 8-tap folds for the LSB-binding same-size chain on BabyBear/Ext4.
//!
//! Grid layout (16 CELLS per vector): the 27-cell `{0,1,inf}^3` window grid
//! is exactly TWO groups — cells 0..16 (the 8 binary cells then 8 infinity
//! cells) and cells 16..32 (11 infinity cells + 5 zero padding cells) — in
//! the same cell numbering as the AVX2/NEON kernels ([`W3_INF`]), so the
//! chain executor reuses [`w3_soa_cell_of_generic`]. Base grids are
//! `[2][16]` u32, ext grids `[2 groups][4 limbs][16]` u32.
//!
//! What differs from the AVX2 kernel besides the lane count:
//! * the 19 infinity cells are extrapolated IN REGISTERS (three permute /
//!   subtract levels, [`avx512::extrapolate`]) instead of 19 scalar
//!   subtractions per slot per row; one 16-tap load serves two rows;
//! * the per-row lazy accumulator (`[2 groups][4 limbs]` even/odd u64
//!   vectors = 16 registers) lives in REGISTERS for the whole program of a
//!   row instead of being loaded and stored around every product;
//! * the row's suffix-eq weighting is lazily accumulated into a per-chunk
//!   u64 accumulator (one REDC per chunk) instead of a canonical ext
//!   multiply-add per row.
//! All arithmetic stays exact modular arithmetic, so the 27-cell
//! accumulators and the folds are byte-identical to the AVX2 kernels' (the
//! unit tests below pin that).
//!
//! The "double loop" the cache asks for is the row loop around the program
//! loop: for one row (a pair of rows per 16-tap load) every slot and form
//! grid is materialized once into an L1-resident scratch (`<= 48 KB` for
//! layer 0's 48 base slots + forms), then the whole program runs over those
//! grids with register accumulators — every reuse of a column's cells is an
//! L1 hit, whatever its distance in the program.

use super::avx512 as k;
use super::avx512::{ExtPerm, ExtTable16, Lazy16, W3Perm};
use super::program::{FormDesc, FormOp, FormRef, ProgramStep};
use crate::gkr::sumcheck::access_and_fold::DisjointAccessQuasiSlice;
use crate::worker::Worker;
use ::field::baby_bear::base::BabyBearField;
use ::field::baby_bear::ext4::BabyBearExt4;
use ::field::Field;
use core::arch::x86_64::*;

pub(crate) const OUT: usize = 27;
/// u32 per base grid: 2 groups x 16 cells
const BS: usize = 32;
/// u32 per ext grid: [2 groups][4 limbs][16 cells]
const ES: usize = 128;
/// u64 per lazy accumulator buffer: [2 groups][4 limbs] x (16 even + 16 odd)
const LAZY: usize = 256;

/// u32 offset of limb `l` of group `g` in an ext grid
#[inline(always)]
const fn eoff(g: usize, l: usize) -> usize {
    16 * (4 * g + l)
}
/// u64 offset of the lazy accumulator of limb `l` of group `g`
#[inline(always)]
const fn loff(g: usize, l: usize) -> usize {
    32 * (4 * g + l)
}

// ---------------------------------------------------------------------------
// grid fills and form ops
// ---------------------------------------------------------------------------

/// Base grids of rows `block` and `block + 1` (one 16-tap load).
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn fill_base_pair(
    dst0: *mut u32,
    dst1: *mut u32,
    src: *const u32,
    block: usize,
    interp: bool,
    pe: &W3Perm,
    po: &W3Perm,
) {
    let v = k::ld(src.add(block * 8));
    let (a0, a1) = if interp {
        k::extrapolate(v, pe)
    } else {
        k::plain_grid(v, pe)
    };
    k::st(dst0, a0);
    k::st(dst0.add(16), a1);
    let (b0, b1) = if interp {
        k::extrapolate(v, po)
    } else {
        k::plain_grid(v, po)
    };
    k::st(dst1, b0);
    k::st(dst1.add(16), b1);
}

/// Ext grid of one row: AoS read, limb split, per-limb extrapolation.
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn fill_ext(
    dst: *mut u32,
    src: *const BabyBearExt4,
    row: usize,
    interp: bool,
    pe: &W3Perm,
    xp: &ExtPerm,
) {
    let limbs = k::transpose_ext8(src.add(row * 8), xp);
    for l in 0..4 {
        let (g0, g1) = if interp {
            k::extrapolate(limbs[l], pe)
        } else {
            k::plain_grid(limbs[l], pe)
        };
        k::st(dst.add(eoff(0, l)), g0);
        k::st(dst.add(eoff(1, l)), g1);
    }
}

#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn form_first<const N: usize>(dst: *mut u32, src: *const u32, op: &FormOp<BabyBearField>) {
    match op {
        FormOp::Add => {
            for i in 0..N {
                k::st(dst.add(16 * i), k::ld(src.add(16 * i)));
            }
        }
        FormOp::Sub => {
            let z = k::zero();
            for i in 0..N {
                k::st(dst.add(16 * i), k::sub16(z, k::ld(src.add(16 * i))));
            }
        }
        FormOp::Mul(c) => {
            let cv = k::bc32(c.raw_u32_value());
            for i in 0..N {
                k::st(dst.add(16 * i), k::mont_mul16(k::ld(src.add(16 * i)), cv));
            }
        }
    }
}

#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn form_acc<const N: usize>(dst: *mut u32, src: *const u32, op: &FormOp<BabyBearField>) {
    match op {
        FormOp::Add => {
            for i in 0..N {
                let p = dst.add(16 * i);
                k::st(p, k::add16(k::ld(p), k::ld(src.add(16 * i))));
            }
        }
        FormOp::Sub => {
            for i in 0..N {
                let p = dst.add(16 * i);
                k::st(p, k::sub16(k::ld(p), k::ld(src.add(16 * i))));
            }
        }
        FormOp::Mul(c) => {
            let cv = k::bc32(c.raw_u32_value());
            for i in 0..N {
                let p = dst.add(16 * i);
                k::st(
                    p,
                    k::add16(k::ld(p), k::mont_mul16(k::ld(src.add(16 * i)), cv)),
                );
            }
        }
    }
}

/// `+= c` on the 8 binary cells only (limb 0 of group 0 for ext grids).
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn form_const(dst: *mut u32, c: BabyBearField) {
    let v = k::ld(dst);
    k::st(
        dst,
        _mm512_mask_mov_epi32(v, 0x00FF, k::add16(v, k::bc32(c.raw_u32_value()))),
    );
}

/// A rest step with its coefficient pre-split into raw limbs (base steps)
/// or pre-built as a lazy multiplication table (ext steps).
#[derive(Clone, Copy)]
enum RStep {
    QuadBB {
        a: usize,
        b: usize,
        c: [u32; 4],
    },
    LinB {
        i: usize,
        c: [u32; 4],
    },
    QuadBE {
        base: usize,
        ext: usize,
        c: [u32; 4],
    },
    QuadEE {
        a: usize,
        b: usize,
        c: [u32; 4],
    },
    LinE {
        i: usize,
        c: [u32; 4],
    },
}

/// The ext steps' coefficient tables, built once per chunk (they are
/// `[[__m512i; 4]; 4]` each, so they stay out of the `RStep` enum).
struct ExtStepTables {
    tables: Vec<ExtTable16>,
}
impl ExtStepTables {
    #[target_feature(enable = "avx512f")]
    unsafe fn new(rest: &[RStep]) -> Self {
        let tables = rest
            .iter()
            .map(|s| match s {
                RStep::QuadBE { c, .. } | RStep::QuadEE { c, .. } | RStep::LinE { c, .. } => {
                    ExtTable16::new(&core::mem::transmute::<[u32; 4], BabyBearExt4>(*c))
                }
                _ => ExtTable16::new(&BabyBearExt4::ZERO),
            })
            .collect();
        Self { tables }
    }
}

fn limbs(c: &BabyBearExt4) -> [u32; 4] {
    unsafe { core::mem::transmute(*c) }
}

fn to_rsteps(steps: &[ProgramStep<BabyBearExt4>]) -> Vec<RStep> {
    steps
        .iter()
        .map(|s| match s {
            ProgramStep::QuadBB { a, b, c } => RStep::QuadBB {
                a: *a as usize,
                b: *b as usize,
                c: limbs(c),
            },
            ProgramStep::LinB { i, c } => RStep::LinB {
                i: *i as usize,
                c: limbs(c),
            },
            ProgramStep::QuadBE { base, ext, c } => RStep::QuadBE {
                base: *base as usize,
                ext: *ext as usize,
                c: limbs(c),
            },
            ProgramStep::QuadEE { a, b, c } => RStep::QuadEE {
                a: *a as usize,
                b: *b as usize,
                c: limbs(c),
            },
            ProgramStep::LinE { i, c } => RStep::LinE {
                i: *i as usize,
                c: limbs(c),
            },
        })
        .collect()
}

#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn bc4(c: &[u32; 4]) -> [__m512i; 4] {
    [k::bc32(c[0]), k::bc32(c[1]), k::bc32(c[2]), k::bc32(c[3])]
}

#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn load_limbs(p: *const u32, g: usize) -> [__m512i; 4] {
    core::array::from_fn(|l| k::ld(p.add(eoff(g, l))))
}

/// REDC the row accumulator, add the reduced-path terms and the additive
/// constant (binary cells only), then lazily accumulate the row weighted by
/// its suffix-eq factor into the chunk accumulator.
#[inline]
#[target_feature(enable = "avx512f")]
unsafe fn finish_row(
    acc: &[[Lazy16; 4]; 2],
    reduced: *mut u32,
    have_reduced: bool,
    const_bcast: &Option<[__m512i; 4]>,
    eq: &ExtTable16,
    cacc: *mut u64,
) {
    let mut red: [[__m512i; 4]; 2] = [[k::zero(); 4]; 2];
    for g in 0..2 {
        for l in 0..4 {
            red[g][l] = acc[g][l].redc();
        }
    }
    if have_reduced {
        for g in 0..2 {
            for l in 0..4 {
                let p = reduced.add(eoff(g, l));
                red[g][l] = k::add16(red[g][l], k::ld(p));
                k::st(p, k::zero());
            }
        }
    }
    if let Some(cb) = const_bcast {
        for l in 0..4 {
            red[0][l] = _mm512_mask_mov_epi32(red[0][l], 0x00FF, k::add16(red[0][l], cb[l]));
        }
    }
    for g in 0..2 {
        let v = red[g];
        let vh: [__m512i; 4] = core::array::from_fn(|l| k::hi64(v[l]));
        let mut ca: [Lazy16; 4] = core::array::from_fn(|l| Lazy16::load(cacc.add(loff(g, l))));
        eq.mla_into(&mut ca, &v, &vh);
        for l in 0..4 {
            ca[l].store(cacc.add(loff(g, l)));
        }
    }
}

/// The gate polynomial of one row of the INITIAL pass over its materialized
/// grids, with register-resident lazy accumulators.
#[allow(clippy::too_many_arguments)]
#[target_feature(enable = "avx512f")]
unsafe fn eval_row_initial(
    bp: *const u32,
    fp: *const u32,
    xp: *const u32,
    prods: &[(FormRef, FormRef, [u32; 4])],
    rest: &[RStep],
    tables: &ExtStepTables,
    r11: __m512i,
    const_bcast: &Option<[__m512i; 4]>,
    eq: &ExtTable16,
    cacc: *mut u64,
) {
    let mut acc: [[Lazy16; 4]; 2] = [[Lazy16::zero(); 4]; 2];
    let mut ticks = 0usize;
    macro_rules! tick {
        () => {
            ticks += 1;
            if ticks == 2 {
                for g in 0..2 {
                    for l in 0..4 {
                        acc[g][l].condsub();
                    }
                }
                ticks = 0;
            }
        };
    }
    // the table paths keep their own two-products cadence: settle a pending
    // base product before them so no accumulator ever holds more than two
    // raw products between conditional subtractions
    macro_rules! settle {
        () => {
            if ticks != 0 {
                for g in 0..2 {
                    for l in 0..4 {
                        acc[g][l].condsub();
                    }
                }
                ticks = 0;
            }
        };
    }
    let grid = |r: &FormRef| -> *const u32 {
        match r {
            FormRef::Slot(i) => bp.add(*i as usize * BS),
            FormRef::Form(i) => fp.add(*i as usize * BS),
        }
    };
    for (a, b, c) in prods.iter() {
        let (pa, pb) = (grid(a), grid(b));
        let cv = bc4(c);
        for g in 0..2 {
            let t = k::mont_mul16(k::ld(pa.add(16 * g)), k::ld(pb.add(16 * g)));
            let th = k::hi64(t);
            for l in 0..4 {
                acc[g][l].mla(cv[l], t, th);
            }
        }
        tick!();
    }
    for (si, step) in rest.iter().enumerate() {
        match step {
            RStep::QuadBB { a, b, c } => {
                let (pa, pb) = (bp.add(a * BS), bp.add(b * BS));
                let cv = bc4(c);
                for g in 0..2 {
                    let t = k::mont_mul16(k::ld(pa.add(16 * g)), k::ld(pb.add(16 * g)));
                    let th = k::hi64(t);
                    for l in 0..4 {
                        acc[g][l].mla(cv[l], t, th);
                    }
                }
                tick!();
            }
            RStep::LinB { i, c } => {
                let cv = bc4(c);
                let t = _mm512_maskz_mov_epi32(0x00FF, k::ld(bp.add(i * BS)));
                let th = k::hi64(t);
                for l in 0..4 {
                    acc[0][l].mla(cv[l], t, th);
                }
                tick!();
            }
            RStep::QuadBE { base, ext, .. } => {
                settle!();
                let tb = &tables.tables[si];
                for g in 0..2 {
                    let bv = k::ld(bp.add(base * BS + 16 * g));
                    let t: [__m512i; 4] = core::array::from_fn(|l| {
                        k::mont_mul16(k::ld(xp.add(ext * ES + eoff(g, l))), bv)
                    });
                    let th: [__m512i; 4] = core::array::from_fn(|l| k::hi64(t[l]));
                    tb.mla_into(&mut acc[g], &t, &th);
                }
            }
            RStep::QuadEE { a, b, .. } => {
                settle!();
                let tb = &tables.tables[si];
                for g in 0..2 {
                    let v = k::soa_ext_mul_lazy(
                        &load_limbs(xp.add(a * ES), g),
                        &load_limbs(xp.add(b * ES), g),
                        r11,
                    );
                    let vh: [__m512i; 4] = core::array::from_fn(|l| k::hi64(v[l]));
                    tb.mla_into(&mut acc[g], &v, &vh);
                }
            }
            RStep::LinE { i, .. } => {
                settle!();
                let tb = &tables.tables[si];
                let raw = load_limbs(xp.add(i * ES), 0);
                let v: [__m512i; 4] =
                    core::array::from_fn(|l| _mm512_maskz_mov_epi32(0x00FF, raw[l]));
                let vh: [__m512i; 4] = core::array::from_fn(|l| k::hi64(v[l]));
                tb.mla_into(&mut acc[0], &v, &vh);
            }
        }
    }
    finish_row(&acc, core::ptr::null_mut(), false, const_bcast, eq, cacc);
}

/// The gate polynomial of one row of a CONTINUING pass (all-ext grids).
#[allow(clippy::too_many_arguments)]
#[target_feature(enable = "avx512f")]
unsafe fn eval_row_ext(
    xp: *const u32,
    fp: *const u32,
    prods: &[(FormRef, FormRef, ExtTable16)],
    quads: &[(usize, usize, ExtTable16)],
    lins: &[(usize, ExtTable16)],
    reduced: *mut u32,
    r11: __m512i,
    const_bcast: &Option<[__m512i; 4]>,
    eq: &ExtTable16,
    cacc: *mut u64,
) {
    let mut acc: [[Lazy16; 4]; 2] = [[Lazy16::zero(); 4]; 2];
    let grid = |r: &FormRef| -> *const u32 {
        match r {
            FormRef::Slot(i) => xp.add(*i as usize * ES),
            FormRef::Form(i) => fp.add(*i as usize * ES),
        }
    };
    for (a, b, tb) in prods.iter() {
        let (pa, pb) = (grid(a), grid(b));
        for g in 0..2 {
            let v = k::soa_ext_mul_lazy(&load_limbs(pa, g), &load_limbs(pb, g), r11);
            let vh: [__m512i; 4] = core::array::from_fn(|l| k::hi64(v[l]));
            tb.mla_into(&mut acc[g], &v, &vh);
        }
    }
    for (a, b, tb) in quads.iter() {
        let (pa, pb) = (xp.add(a * ES), xp.add(b * ES));
        for g in 0..2 {
            let v = k::soa_ext_mul_lazy(&load_limbs(pa, g), &load_limbs(pb, g), r11);
            let vh: [__m512i; 4] = core::array::from_fn(|l| k::hi64(v[l]));
            tb.mla_into(&mut acc[g], &v, &vh);
        }
    }
    for (i, tb) in lins.iter() {
        let raw = load_limbs(xp.add(i * ES), 0);
        let v: [__m512i; 4] = core::array::from_fn(|l| _mm512_maskz_mov_epi32(0x00FF, raw[l]));
        let vh: [__m512i; 4] = core::array::from_fn(|l| k::hi64(v[l]));
        tb.mla_into(&mut acc[0], &v, &vh);
    }
    finish_row(&acc, reduced, false, const_bcast, eq, cacc);
}

/// The chunk accumulator (REDC'd) as the first `OUT` SoA-order cells,
/// exactly like the AVX2 kernel's `finish_soa_acc`.
#[target_feature(enable = "avx512f")]
unsafe fn finish_chunk(cacc: *mut u64, xp: &ExtPerm) -> [BabyBearExt4; OUT] {
    let mut grid = [0u32; ES];
    for g in 0..2 {
        for l in 0..4 {
            k::st(
                grid.as_mut_ptr().add(eoff(g, l)),
                Lazy16::load(cacc.add(loff(g, l))).redc(),
            );
        }
    }
    let mut aos = [BabyBearExt4::ZERO; 32];
    k::untranspose_grid_to_aos(grid.as_ptr(), aos.as_mut_ptr(), xp);
    let mut out = [BabyBearExt4::ZERO; OUT];
    out.copy_from_slice(&aos[..OUT]);
    out
}

fn reduce_chunks(mut chunks: Vec<[BabyBearExt4; OUT]>) -> [BabyBearExt4; OUT] {
    let mut acc = chunks.pop().unwrap();
    for el in chunks.into_iter() {
        for i in 0..OUT {
            acc[i].add_assign(&el[i]);
        }
    }
    acc
}

// ---------------------------------------------------------------------------
// the passes
// ---------------------------------------------------------------------------

/// One thread's chunk of the INITIAL pass: rows `chunk_start ..
/// chunk_start + chunk_size` (even), two rows per 16-tap load.
#[allow(clippy::too_many_arguments)]
#[target_feature(enable = "avx512f")]
unsafe fn initial_chunk(
    base: &[*const u32],
    ext: &[*const BabyBearExt4],
    base_interp: &[bool],
    ext_interp: &[bool],
    forms: &[FormDesc<BabyBearField>],
    prods: &[(FormRef, FormRef, [u32; 4])],
    rest: &[RStep],
    additive_constant: &BabyBearExt4,
    t_suffix: &[BabyBearExt4],
    chunk_start: usize,
    chunk_size: usize,
) -> [BabyBearExt4; OUT] {
    let pe = W3Perm::new(false);
    let po = W3Perm::new(true);
    let xperm = ExtPerm::new();
    let r11 = k::r11v();
    let const_bcast = (!additive_constant.is_zero()).then(|| k::bcast_ext(additive_constant));
    let (nb, ne, nf) = (base.len(), ext.len(), forms.len());
    // rows per fill block (even): the grids of `rb` rows are materialized
    // SLOT-major (rb/2 consecutive lines per slot) before the rows are
    // evaluated one by one, so the source reads are `rb * 32 B` bursts per
    // slot instead of `nb + ne` interleaved 32 B streams. Measured on
    // add/sub layer 0 (49 base slots): 2 rows 319 ms, 8 rows 270, 32 rows
    // 212 (the hardware prefetchers do not track 59 streams); layers with
    // few base slots are best at 2 (their ext grids fill L2 otherwise).
    // Knob `SS_ROW_BLOCK` overrides.
    let rb: usize = std::env::var("SS_ROW_BLOCK")
        .ok()
        .and_then(|v| v.parse().ok())
        .filter(|&b: &usize| b >= 2 && b % 2 == 0 && b <= 64)
        .unwrap_or(if nb >= 24 { 32 } else { 2 });
    let mut base_flat = vec![0u32; nb * rb * BS];
    let mut ext_flat = vec![0u32; ne * rb * ES];
    let mut form_flat = vec![0u32; nf * rb * BS];
    let mut cacc = vec![0u64; LAZY];
    let bptr = base_flat.as_mut_ptr();
    let xptr = ext_flat.as_mut_ptr();
    let fptr = form_flat.as_mut_ptr();
    let cptr = cacc.as_mut_ptr();
    let tables = ExtStepTables::new(rest);

    // scratch is ROW-major: row u's slot/form/ext grid i at (u * n + i) * stride
    let mut block = chunk_start;
    while block < chunk_start + chunk_size {
        let rows_here = rb.min(chunk_start + chunk_size - block);
        debug_assert_eq!(rows_here % 2, 0);
        for (i, src) in base.iter().enumerate() {
            for pr in 0..rows_here / 2 {
                fill_base_pair(
                    bptr.add(((2 * pr) * nb + i) * BS),
                    bptr.add(((2 * pr + 1) * nb + i) * BS),
                    *src,
                    block + 2 * pr,
                    base_interp[i],
                    &pe,
                    &po,
                );
            }
        }
        for (i, src) in ext.iter().enumerate() {
            for u in 0..rows_here {
                fill_ext(
                    xptr.add((u * ne + i) * ES),
                    *src,
                    block + u,
                    ext_interp[i],
                    &pe,
                    &xperm,
                );
            }
        }
        for u in 0..rows_here {
            let bp = bptr.add(u * nb * BS) as *const u32;
            let fpu = fptr.add(u * nf * BS);
            for (f, form) in forms.iter().enumerate() {
                let g = fpu.add(f * BS);
                let mut it = form.members.iter();
                match it.next() {
                    Some((op, idx)) => form_first::<2>(g, bp.add(*idx as usize * BS), op),
                    None => core::ptr::write_bytes(g, 0, BS),
                }
                for (op, idx) in it {
                    form_acc::<2>(g, bp.add(*idx as usize * BS), op);
                }
                if !form.constant.is_zero() {
                    form_const(g, form.constant);
                }
            }
            let eq = ExtTable16::new(&t_suffix[block + u]);
            eval_row_initial(
                bp,
                fpu,
                xptr.add(u * ne * ES),
                prods,
                rest,
                &tables,
                r11,
                &const_bcast,
                &eq,
                cptr,
            );
        }
        block += rows_here;
    }
    finish_chunk(cptr, &xperm)
}

/// INITIAL window-3 pass over the layer's original base/ext columns (the
/// AVX-512 twin of `lsb_soa_full_parallel_w3::<2>`): `rows` must be even.
#[allow(clippy::too_many_arguments)]
pub(crate) fn lsb_soa_full_parallel_w3(
    base_field_inputs: &[DisjointAccessQuasiSlice<BabyBearField, false>],
    ext_field_inputs: &[DisjointAccessQuasiSlice<BabyBearExt4, false>],
    base_interp: &[bool],
    ext_interp: &[bool],
    forms: &[FormDesc<BabyBearField>],
    products: &[(FormRef, FormRef, BabyBearExt4)],
    rest_steps: &[ProgramStep<BabyBearExt4>],
    additive_constant: &BabyBearExt4,
    t_suffix: &[BabyBearExt4],
    rows: usize,
    worker: &Worker,
) -> [BabyBearExt4; OUT] {
    use crate::gkr::PAR_THRESHOLD;
    const U: usize = 2;
    assert_eq!(t_suffix.len(), rows);
    assert_eq!(rows % U, 0);
    let num_blocks = rows / U;
    let geometry = worker.get_geometry_with_threshold(num_blocks, (PAR_THRESHOLD / U).max(1));
    let mut acc_chunks = vec![[BabyBearExt4::ZERO; OUT]; geometry.num_chunks];
    // timing-experiment knobs (the proof diverges; never set in production):
    // SS_SKIP_PRODUCTS=1 drops the factored products, SS_SKIP_EXT_STEPS=1 the
    // ext rest steps (QuadBE/QuadEE/LinE), SS_SKIP_BASE_STEPS=1 the base rest
    // steps (QuadBB/LinB)
    let knob = |name: &str| std::env::var(name).map(|v| v == "1").unwrap_or(false);
    let prods: Vec<(FormRef, FormRef, [u32; 4])> = if knob("SS_SKIP_PRODUCTS") {
        Vec::new()
    } else {
        products
            .iter()
            .map(|(a, b, c)| (*a, *b, limbs(c)))
            .collect()
    };
    let (skip_ext, skip_base) = (knob("SS_SKIP_EXT_STEPS"), knob("SS_SKIP_BASE_STEPS"));
    let rest: Vec<RStep> = to_rsteps(rest_steps)
        .into_iter()
        .filter(|s| match s {
            RStep::QuadBB { .. } | RStep::LinB { .. } => !skip_base,
            _ => !skip_ext,
        })
        .collect();
    let base_ptrs: Vec<usize> = base_field_inputs.iter().map(|s| s.ptr as usize).collect();
    let ext_ptrs: Vec<usize> = ext_field_inputs.iter().map(|s| s.ptr as usize).collect();

    worker.scope_with_threshold(num_blocks, (PAR_THRESHOLD / U).max(1), |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx) * U;
            let chunk_size = geometry.get_chunk_size(thread_idx) * U;
            let acc_dst = it.next().unwrap();
            let (base_ptrs, ext_ptrs, prods, rest) = (&base_ptrs, &ext_ptrs, &prods, &rest);
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                let base: Vec<*const u32> = base_ptrs.iter().map(|&p| p as *const u32).collect();
                let ext: Vec<*const BabyBearExt4> =
                    ext_ptrs.iter().map(|&p| p as *const BabyBearExt4).collect();
                *acc_dst = initial_chunk(
                    &base,
                    &ext,
                    base_interp,
                    ext_interp,
                    forms,
                    prods,
                    rest,
                    additive_constant,
                    t_suffix,
                    chunk_start,
                    chunk_size,
                );
            })
        }
    });
    reduce_chunks(acc_chunks)
}

/// One thread's chunk of a CONTINUING pass.
#[allow(clippy::too_many_arguments)]
#[target_feature(enable = "avx512f")]
unsafe fn ext_chunk(
    ext: &[*const BabyBearExt4],
    interp: &[bool],
    forms: &[FormDesc<BabyBearField>],
    products: &[(FormRef, FormRef, BabyBearExt4)],
    quads: &[(u16, u16, BabyBearExt4)],
    linear_terms: &[(u16, BabyBearExt4)],
    additive_constant: &BabyBearExt4,
    t_suffix: &[BabyBearExt4],
    chunk_start: usize,
    chunk_size: usize,
) -> [BabyBearExt4; OUT] {
    let pe = W3Perm::new(false);
    let xperm = ExtPerm::new();
    let r11 = k::r11v();
    let const_bcast = (!additive_constant.is_zero()).then(|| k::bcast_ext(additive_constant));
    let (ne, nf) = (ext.len(), forms.len());
    let mut ext_flat = vec![0u32; ne * ES];
    let mut form_flat = vec![0u32; nf * ES];
    let mut reduced = vec![0u32; ES];
    let mut cacc = vec![0u64; LAZY];
    let xptr = ext_flat.as_mut_ptr();
    let fptr = form_flat.as_mut_ptr();
    let rptr = reduced.as_mut_ptr();
    let cptr = cacc.as_mut_ptr();
    let prods: Vec<(FormRef, FormRef, ExtTable16)> = products
        .iter()
        .map(|(a, b, c)| (*a, *b, ExtTable16::new(c)))
        .collect();
    let quads: Vec<(usize, usize, ExtTable16)> = quads
        .iter()
        .map(|(a, b, c)| (*a as usize, *b as usize, ExtTable16::new(c)))
        .collect();
    let lins: Vec<(usize, ExtTable16)> = linear_terms
        .iter()
        .map(|(i, c)| (*i as usize, ExtTable16::new(c)))
        .collect();

    for row in chunk_start..chunk_start + chunk_size {
        for (i, src) in ext.iter().enumerate() {
            fill_ext(xptr.add(i * ES), *src, row, interp[i], &pe, &xperm);
        }
        for (f, form) in forms.iter().enumerate() {
            let g = fptr.add(f * ES);
            let mut it = form.members.iter();
            match it.next() {
                Some((op, idx)) => form_first::<8>(g, xptr.add(*idx as usize * ES), op),
                None => core::ptr::write_bytes(g, 0, ES),
            }
            for (op, idx) in it {
                form_acc::<8>(g, xptr.add(*idx as usize * ES), op);
            }
            if !form.constant.is_zero() {
                form_const(g, form.constant);
            }
        }
        let eq = ExtTable16::new(&t_suffix[row]);
        eval_row_ext(
            xptr,
            fptr,
            &prods,
            &quads,
            &lins,
            rptr,
            r11,
            &const_bcast,
            &eq,
            cptr,
        );
    }
    finish_chunk(cptr, &xperm)
}

/// CONTINUING window-3 pass over the folded (all-ext) tables (the AVX-512
/// twin of `lsb_soa_ext_pass_parallel_w3`).
#[allow(clippy::too_many_arguments)]
pub(crate) fn lsb_soa_ext_pass_parallel_w3(
    ext_inputs: &[DisjointAccessQuasiSlice<BabyBearExt4, false>],
    interp: &[bool],
    forms: &[FormDesc<BabyBearField>],
    products: &[(FormRef, FormRef, BabyBearExt4)],
    quads: &[(u16, u16, BabyBearExt4)],
    linear_terms: &[(u16, BabyBearExt4)],
    additive_constant: &BabyBearExt4,
    t_suffix: &[BabyBearExt4],
    rows: usize,
    worker: &Worker,
) -> [BabyBearExt4; OUT] {
    use crate::gkr::PAR_THRESHOLD;
    assert_eq!(t_suffix.len(), rows);
    assert_eq!(interp.len(), ext_inputs.len());
    let geometry = worker.get_geometry_with_threshold(rows, PAR_THRESHOLD);
    let mut acc_chunks = vec![[BabyBearExt4::ZERO; OUT]; geometry.num_chunks];
    let ext_ptrs: Vec<usize> = ext_inputs.iter().map(|s| s.ptr as usize).collect();

    worker.scope_with_threshold(rows, PAR_THRESHOLD, |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let acc_dst = it.next().unwrap();
            let ext_ptrs = &ext_ptrs;
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                let ext: Vec<*const BabyBearExt4> =
                    ext_ptrs.iter().map(|&p| p as *const BabyBearExt4).collect();
                *acc_dst = ext_chunk(
                    &ext,
                    interp,
                    forms,
                    products,
                    quads,
                    linear_terms,
                    additive_constant,
                    t_suffix,
                    chunk_start,
                    chunk_size,
                );
            })
        }
    });
    reduce_chunks(acc_chunks)
}

// ---------------------------------------------------------------------------
// LSB-layout 8-tap folds, 16 output rows per call
// ---------------------------------------------------------------------------

#[target_feature(enable = "avx512f")]
unsafe fn fold_base_chunk(
    src: *const u32,
    dst: *mut BabyBearExt4,
    weights: &[BabyBearExt4; 8],
    blocks: core::ops::Range<usize>,
) {
    let xp = ExtPerm::new();
    let w: [[__m512i; 4]; 8] = core::array::from_fn(|i| k::bcast_ext(&weights[i]));
    for blk in blocks {
        let p = src.add(blk * 128);
        let v: [__m512i; 8] = core::array::from_fn(|r| k::ld(p.add(16 * r)));
        let taps = k::transpose_taps16(&v, &xp);
        let mut acc = [Lazy16::zero(); 4];
        for i in 0..8 {
            let th = k::hi64(taps[i]);
            for l in 0..4 {
                acc[l].mla(w[i][l], taps[i], th);
            }
            if i % 2 == 1 {
                for l in 0..4 {
                    acc[l].condsub();
                }
            }
        }
        let limbs: [__m512i; 4] = core::array::from_fn(|l| acc[l].redc());
        k::store_ext16(&limbs, dst.add(16 * blk), &xp);
    }
}

#[target_feature(enable = "avx512f")]
unsafe fn fold_ext_chunk(
    src: *const BabyBearExt4,
    dst: *mut BabyBearExt4,
    weights: &[BabyBearExt4; 8],
    blocks: core::ops::Range<usize>,
) {
    let xp = ExtPerm::new();
    let tables: [ExtTable16; 8] = core::array::from_fn(|i| ExtTable16::new(&weights[i]));
    for blk in blocks {
        let base = src.add(blk * 128);
        let mut acc = [Lazy16::zero(); 4];
        for i in 0..8 {
            // rows 4j..4j+4, tap i: elements base[(4j+q)*8 + i]
            let z: [__m512i; 4] = core::array::from_fn(|j| {
                let e = |q: usize| _mm_loadu_si128(base.add((4 * j + q) * 8 + i) as *const __m128i);
                let mut v = _mm512_castsi128_si512(e(0));
                v = _mm512_inserti32x4::<1>(v, e(1));
                v = _mm512_inserti32x4::<2>(v, e(2));
                _mm512_inserti32x4::<3>(v, e(3))
            });
            let limbs = k::transpose_ext16_vecs(&z, &xp);
            let lh: [__m512i; 4] = core::array::from_fn(|l| k::hi64(limbs[l]));
            tables[i].mla_into(&mut acc, &limbs, &lh);
        }
        let limbs: [__m512i; 4] = core::array::from_fn(|l| acc[l].redc());
        k::store_ext16(&limbs, dst.add(16 * blk), &xp);
    }
}

/// 8-tap Lagrange fold of a base column in LSB layout, 16 output rows per
/// block (requires `dst.len() % 16 == 0`).
pub(crate) fn lsb_fold_base_parallel(
    src_ptr: *const u8,
    dst: &mut [BabyBearExt4],
    weights: &[BabyBearExt4; 8],
    worker: &Worker,
) {
    use crate::gkr::PAR_THRESHOLD;
    let rows = dst.len();
    assert_eq!(rows % 16, 0);
    let blocks = rows / 16;
    let dst_addr = dst.as_mut_ptr() as usize;
    let src_addr = src_ptr as usize;
    worker.scope_with_threshold(blocks, (PAR_THRESHOLD / 16).max(1), |scope, geometry| {
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                fold_base_chunk(
                    src_addr as *const u32,
                    dst_addr as *mut BabyBearExt4,
                    weights,
                    chunk_start..chunk_start + chunk_size,
                );
            })
        }
    });
}

/// 8-tap Lagrange fold of an ext column in LSB layout, 16 output rows per
/// block (requires `dst.len() % 16 == 0`).
pub(crate) fn lsb_fold_ext_parallel(
    src_ptr: *const u8,
    dst: &mut [BabyBearExt4],
    weights: &[BabyBearExt4; 8],
    worker: &Worker,
) {
    use crate::gkr::PAR_THRESHOLD;
    let rows = dst.len();
    assert_eq!(rows % 16, 0);
    let blocks = rows / 16;
    let dst_addr = dst.as_mut_ptr() as usize;
    let src_addr = src_ptr as usize;
    worker.scope_with_threshold(blocks, (PAR_THRESHOLD / 16).max(1), |scope, geometry| {
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                fold_ext_chunk(
                    src_addr as *const BabyBearExt4,
                    dst_addr as *mut BabyBearExt4,
                    weights,
                    chunk_start..chunk_start + chunk_size,
                );
            })
        }
    });
}

#[cfg(test)]
mod tests {
    use super::super::lsb_avx2;
    use super::*;
    use ::field::{FieldExtension, PrimeField};

    fn pseudo_base(seed: &mut u64) -> BabyBearField {
        *seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        BabyBearField::from_u32_with_reduction((*seed >> 33) as u32)
    }
    fn pseudo_ext(seed: &mut u64) -> BabyBearExt4 {
        BabyBearExt4::from_array_of_base(core::array::from_fn(|_| pseudo_base(seed)))
    }

    fn have_avx512() -> bool {
        let ok = is_x86_feature_detected!("avx512f");
        if !ok {
            eprintln!("avx512f not available: skipping");
        }
        ok
    }

    /// A synthetic program with every step kind over `nb` base and `ne` ext
    /// slots (all interpolated), 3 forms, factored products, expanded quads,
    /// linear terms and a constant.
    fn synthetic_program(
        nb: usize,
        ne: usize,
        seed: &mut u64,
    ) -> (
        Vec<FormDesc<BabyBearField>>,
        Vec<(FormRef, FormRef, BabyBearExt4)>,
        Vec<ProgramStep<BabyBearExt4>>,
        BabyBearExt4,
    ) {
        let forms = vec![
            FormDesc {
                members: vec![(FormOp::Add, 0), (FormOp::Sub, 1)],
                constant: pseudo_base(seed),
            },
            FormDesc {
                members: vec![(FormOp::Mul(pseudo_base(seed)), 2), (FormOp::Add, 3)],
                constant: BabyBearField::ZERO,
            },
            FormDesc {
                members: vec![(FormOp::Add, 4)],
                constant: pseudo_base(seed),
            },
        ];
        let products = vec![
            (FormRef::Form(0), FormRef::Form(1), pseudo_ext(seed)),
            (FormRef::Slot(5), FormRef::Form(2), pseudo_ext(seed)),
            (FormRef::Slot(6), FormRef::Slot(7), pseudo_ext(seed)),
            (FormRef::Form(2), FormRef::Form(2), pseudo_ext(seed)),
            (FormRef::Slot(1), FormRef::Slot(2), pseudo_ext(seed)),
        ];
        let mut rest = vec![
            ProgramStep::QuadBB {
                a: 3,
                b: 4,
                c: pseudo_ext(seed),
            },
            ProgramStep::LinB {
                i: 0,
                c: pseudo_ext(seed),
            },
            ProgramStep::LinB {
                i: (nb - 1) as u16,
                c: pseudo_ext(seed),
            },
            ProgramStep::QuadBB {
                a: 0,
                b: 0,
                c: pseudo_ext(seed),
            },
        ];
        if ne > 0 {
            rest.push(ProgramStep::QuadBE {
                base: 2,
                ext: 0,
                c: pseudo_ext(seed),
            });
            rest.push(ProgramStep::LinE {
                i: (ne - 1) as u16,
                c: pseudo_ext(seed),
            });
            if ne > 1 {
                rest.push(ProgramStep::QuadEE {
                    a: 0,
                    b: 1,
                    c: pseudo_ext(seed),
                });
            }
        }
        (forms, products, rest, pseudo_ext(seed))
    }

    #[test]
    fn avx512_initial_pass_matches_avx2() {
        if !have_avx512() {
            return;
        }
        let worker = Worker::new_with_num_threads(3);
        let mut seed = 11u64;
        // slot nb-1 stays non-interpolated: it is read by LinB only (binary
        // cells), never at the infinity cells
        let (nb, ne, rows) = (9usize, 2usize, 1usize << 9);
        let base: Vec<Vec<BabyBearField>> = (0..nb)
            .map(|_| (0..8 * rows).map(|_| pseudo_base(&mut seed)).collect())
            .collect();
        let ext: Vec<Vec<BabyBearExt4>> = (0..ne)
            .map(|_| (0..8 * rows).map(|_| pseudo_ext(&mut seed)).collect())
            .collect();
        let t: Vec<BabyBearExt4> = (0..rows).map(|_| pseudo_ext(&mut seed)).collect();
        let (forms, products, rest, constant) = synthetic_program(nb, ne, &mut seed);
        let mut base_interp = vec![true; nb];
        base_interp[nb - 1] = false;
        let ext_interp = vec![true; ne];
        let bq: Vec<_> = base
            .iter()
            .map(|v| DisjointAccessQuasiSlice::<_, false>::from_init_slice(v))
            .collect();
        let eq: Vec<_> = ext
            .iter()
            .map(|v| DisjointAccessQuasiSlice::<_, false>::from_init_slice(v))
            .collect();
        let want = lsb_avx2::lsb_soa_full_parallel_w3::<2>(
            &bq,
            &eq,
            &base_interp,
            &ext_interp,
            &forms,
            &products,
            &rest,
            &constant,
            &t,
            rows,
            &worker,
        );
        let got = lsb_soa_full_parallel_w3(
            &bq,
            &eq,
            &base_interp,
            &ext_interp,
            &forms,
            &products,
            &rest,
            &constant,
            &t,
            rows,
            &worker,
        );
        assert_eq!(got, want);
    }

    #[test]
    fn avx512_continuing_pass_matches_avx2() {
        if !have_avx512() {
            return;
        }
        let worker = Worker::new_with_num_threads(3);
        let mut seed = 23u64;
        // slot n-1 stays non-interpolated: linear use only (the AVX2 kernel
        // leaves a non-interpolated ext slot's infinity cells as stale
        // scratch, which production never reads)
        let (n, rows) = (11usize, 1usize << 9);
        let ext: Vec<Vec<BabyBearExt4>> = (0..n)
            .map(|_| (0..8 * rows).map(|_| pseudo_ext(&mut seed)).collect())
            .collect();
        let t: Vec<BabyBearExt4> = (0..rows).map(|_| pseudo_ext(&mut seed)).collect();
        let (forms, products, _rest, constant) = synthetic_program(n, 0, &mut seed);
        let quads = vec![
            (3u16, 4u16, pseudo_ext(&mut seed)),
            (0, 0, pseudo_ext(&mut seed)),
            (8, 9, pseudo_ext(&mut seed)),
        ];
        let lins = vec![
            (0u16, pseudo_ext(&mut seed)),
            (9, pseudo_ext(&mut seed)),
            ((n - 1) as u16, pseudo_ext(&mut seed)),
        ];
        let mut interp = vec![true; n];
        interp[n - 1] = false;
        let q: Vec<_> = ext
            .iter()
            .map(|v| DisjointAccessQuasiSlice::<_, false>::from_init_slice(v))
            .collect();
        let want = lsb_avx2::lsb_soa_ext_pass_parallel_w3::<2>(
            &q, &interp, &forms, &products, &quads, &lins, &constant, &t, rows, &worker,
        );
        let got = lsb_soa_ext_pass_parallel_w3(
            &q, &interp, &forms, &products, &quads, &lins, &constant, &t, rows, &worker,
        );
        assert_eq!(got, want);
    }

    #[test]
    fn avx512_folds_match_avx2() {
        if !have_avx512() {
            return;
        }
        let worker = Worker::new_with_num_threads(3);
        let mut seed = 37u64;
        let rows = 1usize << 8;
        let weights: [BabyBearExt4; 8] = core::array::from_fn(|_| pseudo_ext(&mut seed));
        let base: Vec<BabyBearField> = (0..8 * rows).map(|_| pseudo_base(&mut seed)).collect();
        let ext: Vec<BabyBearExt4> = (0..8 * rows).map(|_| pseudo_ext(&mut seed)).collect();
        let mut want = vec![BabyBearExt4::ZERO; rows];
        let mut got = vec![BabyBearExt4::ZERO; rows];
        lsb_avx2::lsb_fold_base_soa_parallel(
            base.as_ptr() as *const u8,
            &mut want,
            &weights,
            &worker,
        );
        lsb_fold_base_parallel(base.as_ptr() as *const u8, &mut got, &weights, &worker);
        assert_eq!(got, want, "base fold");
        lsb_avx2::lsb_fold_ext_soa_parallel(
            ext.as_ptr() as *const u8,
            &mut want,
            &weights,
            &worker,
        );
        lsb_fold_ext_parallel(ext.as_ptr() as *const u8, &mut got, &weights, &worker);
        assert_eq!(got, want, "ext fold");
    }
}
