//! Artificial LSB-binding test: the window (or uniskip) variables are the LOW
//! bits of the trace index instead of the top bits, so one row's 2^k packed
//! values are CONTIGUOUS in memory.
//!
//! # Reading order (entry point for the uniskip implementation)
//!
//! 1. **Protocol shape**: the `[LSB-CHAIN]` block in `bench.rs`
//!    (`run_windowed_sumcheck_benchmarks`, search for "full 24-round chain")
//!    -- its header comment defines the notation (packed polys, q_g, T_g,
//!    w3_g, folding) and the telescoping identity every pass is checked
//!    against.
//! 2. **One uniskip pass over mixed base/ext columns**:
//!    [`lsb_soa_full_parallel`] below (instantiated with NG=4/NBIN=4/OUT=16
//!    for k=3 uniskip) -- the per-row steps are annotated in place.
//! 3. **One pass over already-folded (all-ext) columns**:
//!    [`lsb_uniskip_ext_pass_parallel`] -- same steps, ext-only kernels,
//!    fully lazy accumulation.
//! 4. **The LDE kernel**: `neon::lsb_lde8_base_mat` (Lagrange-matrix form,
//!    the fastest) or `neon::lsb_lde8_base` (the NTT form the comments
//!    explain first); `neon::soa_lde8` for ext values.
//! 5. **The fold**: `neon::lsb_soa_fold8_base` / `lsb_soa_fold8_ext` wrapped
//!    by [`lsb_fold_base_soa_parallel`] / [`lsb_fold_ext_soa_parallel`].
//!
//! # What one uniskip pass computes
//!
//! For every "row" (= group of 8 adjacent trace points, the 3 low boolean
//! variables packed into one univariate) the evaluator builds each column's
//! 16 evaluations (8 on H, 8 on the coset via LDE), evaluates the gate
//! polynomial G at all 16 points cellwise, weights the row's 16 G-values by
//! the scalar suffix-eq factor T(row), and accumulates. The result is the
//! packed sum-poly q at 16 points -- enough to determine it (deg q <= 14).
//!
//! # Where eq went
//!
//! The eq polynomial over the 3 skipped variables is NOT multiplied into the
//! per-point evaluation: the prover only applies the per-row scalar T(row)
//! (`soa_apply_eq_*`, one ext mul per row), and the window part w3 is folded
//! into the CLAIM by weighting q's 8 H-values -- verifier-side, 8 multiplies
//! per pass. That is why eq shows up as only 2-5% in the [LSB-SPLIT] phase
//! breakdown, and why the term kernels contain no eq logic at all.
//!
//! Compute engine: the SoA kernel suite, reinterpreted. In the MSB SoA layout
//! one vector holds 4 ROWS of a cell; here one vector holds 4 consecutive
//! CELLS of one row. Base grids need no conversion at all -- contiguous
//! vector loads of the row's taps are already "SoA" over cell groups. Ext
//! values are transposed to limb-major SoA per group of 4 cells
//! (`soa_transpose_ext4`), which unlocks the lazy-u64 accumulation and SoA
//! ext-mul kernels; ext LDE runs per limb with the in-register base NTTs.
//! Per-poly scratch stays a single row: 2^k cells for uniskip, 28 (27 + one
//! dummy pad cell) for window-3.
//!
//! `U` unrolls the row loop (an outer-loop analog of the MSB 4-row
//! vectorization): U rows' grids are filled, then every term op is applied to
//! all U rows before the next op, amortizing program dispatch.
//!
//! Accumulators use the LSB cell convention and are NOT comparable to the MSB
//! accumulators cell-by-cell; the bench cross-checks the eq-weighted claim
//! (which is layout-independent) plus full/bounded/unrolled bitwise identity.
//!
//! Window-3 cell layout: cells 0..8 = binary taps in natural low-bit order
//! (b = 4*x0 + 2*x1 + x2), cells 8..27 = infinity extrapolations per
//! [`W3_INF`], cell 27 = padding. Uniskip layout: cells 0..K = values on H
//! (natural order), K..2K = values on the coset gamma*H.

use super::*;

use super::neon;
use super::program::{FormOp, ProgramStep, TiledStep};
use core::arch::aarch64::{uint32x4_t, vld1q_u32, vst1q_u32};

use ::field::baby_bear::ext4::BabyBearExt4;

const P: u32 = 0x78000001;

// phase-split mask bits (a disabled phase is skipped in the row loop)
pub const PH_FILL_BASE: u32 = 1;
pub const PH_FILL_EXT: u32 = 2;
pub const PH_FORMS: u32 = 4;
pub const PH_LAZY: u32 = 8; // base*base products + base linear terms
pub const PH_EXT: u32 = 16; // base*ext, ext*ext, ext linear, constant
pub const PH_EQ: u32 = 32; // lazy finalize + eq application + accumulate
pub const PH_ALL: u32 = 63;

/// (dst, hi, lo): cell `dst` = cell `hi` - cell `lo`. Levels ordered so later
/// entries may reference earlier destinations. Coordinates (x0, x1, x2) with
/// binary cell b = 4*x0 + 2*x1 + x2:
/// * cells  8..12: (x0, x1, inf)  at 8 + 2*x0 + x1
/// * cells 12..18: (x0, inf, c)   at 12 + 3*x0 + c, c in {0, 1, inf}
/// * cells 18..27: (inf, b, c)    at 18 + 3*b + c, b/c in {0, 1, inf}
const W3_INF: [(u8, u8, u8); 19] = [
    (8, 1, 0),
    (9, 3, 2),
    (10, 5, 4),
    (11, 7, 6),
    (12, 2, 0),
    (13, 3, 1),
    (14, 9, 8),
    (15, 6, 4),
    (16, 7, 5),
    (17, 11, 10),
    (18, 4, 0),
    (19, 5, 1),
    (20, 10, 8),
    (21, 6, 2),
    (22, 7, 3),
    (23, 11, 9),
    (24, 15, 12),
    (25, 16, 13),
    (26, 17, 14),
];

#[inline(always)]
unsafe fn lsb_read_base_w3(dst: *mut u32, src: *const u32, row: usize, interpolate: bool) {
    let p = src.add(row * 8);
    vst1q_u32(dst, vld1q_u32(p));
    vst1q_u32(dst.add(4), vld1q_u32(p.add(4)));
    if interpolate {
        for (d, hi, lo) in W3_INF {
            let (a, b) = (*dst.add(hi as usize), *dst.add(lo as usize));
            *dst.add(d as usize) = if a >= b { a - b } else { a + P - b };
        }
    }
}

#[inline(always)]
unsafe fn lsb_read_ext_w3_aos(
    dst: *mut BabyBearExt4,
    src: *const BabyBearExt4,
    row: usize,
    interpolate: bool,
) {
    core::ptr::copy_nonoverlapping(src.add(row * 8), dst, 8);
    if interpolate {
        for (d, hi, lo) in W3_INF {
            let mut v = *dst.add(hi as usize);
            v.sub_assign(&*dst.add(lo as usize));
            *dst.add(d as usize) = v;
        }
    }
}

/// window-3 ext fill: AoS read + extrapolation into `tmp` (28 cells), then
/// limb-major transpose into the 7-group SoA grid.
#[inline(always)]
unsafe fn fill_ext_w3_soa(
    grid: *mut u32,
    src: *const BabyBearExt4,
    row: usize,
    interpolate: bool,
    tmp: *mut BabyBearExt4,
) {
    lsb_read_ext_w3_aos(tmp, src, row, interpolate);
    for g in 0..7 {
        let t = neon::soa_transpose_ext4(tmp.add(4 * g));
        neon::soa_store_cell(grid.add(16 * g), &t);
    }
}

/// In-register base LDE tables for the two uniskip sizes.
pub enum LsbLdeAny {
    K8(neon::LsbLde8Tables),
    K8Mat(neon::LsbLde8MatTables),
    K64(neon::LsbLde64Tables),
}

#[inline(always)]
unsafe fn fill_base_uniskip(grid: *mut u32, src: *const u32, row: usize, tables: &LsbLdeAny) {
    match tables {
        LsbLdeAny::K8(bt) => {
            let p = src.add(row * 8);
            let h = [vld1q_u32(p), vld1q_u32(p.add(4))];
            let coset = neon::lsb_lde8_base_lazy(h, bt);
            vst1q_u32(grid, h[0]);
            vst1q_u32(grid.add(4), h[1]);
            vst1q_u32(grid.add(8), coset[0]);
            vst1q_u32(grid.add(12), coset[1]);
        }
        LsbLdeAny::K8Mat(bt) => {
            let p = src.add(row * 8);
            let h = [vld1q_u32(p), vld1q_u32(p.add(4))];
            let coset = neon::lsb_lde8_base_mat(h, bt);
            vst1q_u32(grid, h[0]);
            vst1q_u32(grid.add(4), h[1]);
            vst1q_u32(grid.add(8), coset[0]);
            vst1q_u32(grid.add(12), coset[1]);
        }
        LsbLdeAny::K64(bt) => {
            let p = src.add(row * 64);
            let h: [uint32x4_t; 16] = core::array::from_fn(|m| vld1q_u32(p.add(4 * m)));
            let coset = neon::lsb_lde64_base(&h, bt);
            for m in 0..16 {
                vst1q_u32(grid.add(4 * m), h[m]);
                vst1q_u32(grid.add(64 + 4 * m), coset[m]);
            }
        }
    }
}

/// uniskip ext fill: transpose K AoS elements to limb-major SoA (H half),
/// then run the base in-register NTT once per limb for the coset half.
#[inline(always)]
unsafe fn fill_ext_uniskip_soa(grid: *mut u32, src: *const u32, row: usize, tables: &LsbLdeAny) {
    match tables {
        LsbLdeAny::K8(bt) => {
            let p = src.add(row * 32) as *const BabyBearExt4;
            for g in 0..2 {
                let t = neon::soa_transpose_ext4(p.add(4 * g));
                neon::soa_store_cell(grid.add(16 * g), &t);
            }
            for l in 0..4 {
                let h = [vld1q_u32(grid.add(4 * l)), vld1q_u32(grid.add(16 + 4 * l))];
                let coset = neon::lsb_lde8_base_lazy(h, bt);
                vst1q_u32(grid.add(32 + 4 * l), coset[0]);
                vst1q_u32(grid.add(48 + 4 * l), coset[1]);
            }
        }
        LsbLdeAny::K8Mat(bt) => {
            let p = src.add(row * 32) as *const BabyBearExt4;
            for g in 0..2 {
                let t = neon::soa_transpose_ext4(p.add(4 * g));
                neon::soa_store_cell(grid.add(16 * g), &t);
            }
            for l in 0..4 {
                let h = [vld1q_u32(grid.add(4 * l)), vld1q_u32(grid.add(16 + 4 * l))];
                let coset = neon::lsb_lde8_base_mat(h, bt);
                vst1q_u32(grid.add(32 + 4 * l), coset[0]);
                vst1q_u32(grid.add(48 + 4 * l), coset[1]);
            }
        }
        LsbLdeAny::K64(bt) => {
            let p = src.add(row * 256) as *const BabyBearExt4;
            for g in 0..16 {
                let t = neon::soa_transpose_ext4(p.add(4 * g));
                neon::soa_store_cell(grid.add(16 * g), &t);
            }
            for l in 0..4 {
                let h: [uint32x4_t; 16] =
                    core::array::from_fn(|g| vld1q_u32(grid.add(16 * g + 4 * l)));
                let coset = neon::lsb_lde64_base(&h, bt);
                for g in 0..16 {
                    vst1q_u32(grid.add(16 * (16 + g) + 4 * l), coset[g]);
                }
            }
        }
    }
}

#[inline(always)]
unsafe fn apply_form_op<F: PrimeField, const NG: usize>(
    dst: *mut u32,
    src: *const u32,
    op: &FormOp<F>,
) {
    match op {
        FormOp::Add => neon::soa_base_form_add_n::<NG>(dst, src),
        FormOp::Sub => neon::soa_base_form_sub_n::<NG>(dst, src),
        FormOp::Mul(c) => {
            neon::soa_base_form_muladd_n::<NG>(dst, src, *(c as *const F as *const _))
        }
    }
}

macro_rules! reduce_chunks {
    ($chunks:expr, $n:expr) => {{
        let mut acc = $chunks.pop().unwrap();
        for el in $chunks.into_iter() {
            for i in 0..$n {
                acc[i].add_assign(&el[i]);
            }
        }
        acc
    }};
}

/// Full-scratch LSB evaluator over the SoA engine. `NG` = number of 4-cell
/// SoA groups (7 for window-3, K/2 for uniskip), `NBIN` = groups touched by
/// linear terms / the constant (2 for window-3, `NG` for uniskip), `OUT` =
/// returned cell count (27 / 4*NG), `U` = row-unroll factor.
/// `tables: None` selects window-3 mode (interp readers), `Some` uniskip.
pub fn lsb_soa_full_parallel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const NG: usize,
    const NBIN: usize,
    const OUT: usize,
    const U: usize,
>(
    base_field_inputs: &[DisjointAccessQuasiSlice<F, false>],
    ext_field_inputs: &[DisjointAccessQuasiSlice<E, false>],
    base_interp: &[bool],
    ext_interp: &[bool],
    tables: Option<&LsbLdeAny>,
    forms: &[Vec<(FormOp<F>, u16)>],
    products: &[(u16, u16, E)],
    rest_steps: &[ProgramStep<E>],
    additive_constant: &E,
    t_suffix: &[E],
    rows: usize,
    worker: &Worker,
    mask: u32,
) -> [E; OUT] {
    use crate::gkr::PAR_THRESHOLD;

    if const { !neon::is_bb_pair::<F, E>() } {
        unreachable!("LSB variant is BabyBear/Ext4-specific");
    }
    assert_eq!(t_suffix.len(), rows);
    assert_eq!(rows % U, 0);
    let num_blocks = rows / U;
    let geometry = worker.get_geometry_with_threshold(num_blocks, PAR_THRESHOLD / U);
    let mut acc_chunks = vec![[E::ZERO; OUT]; geometry.num_chunks];

    worker.scope_with_threshold(num_blocks, PAR_THRESHOLD / U, |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx) * U;
            let chunk_size = geometry.get_chunk_size(thread_idx) * U;
            let base_field_inputs = base_field_inputs.to_vec();
            let ext_field_inputs = ext_field_inputs.to_vec();
            let acc_dst = it.next().unwrap();

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                let ec = |c: &E| -> &BabyBearExt4 { &*(c as *const E as *const _) };
                let r11v = neon::soa_r11v();
                let const_bcast = neon::soa_broadcast_ext(ec(additive_constant));
                let has_const = !additive_constant.is_zero();
                let bs = 4 * NG; // base grid stride (u32)
                let es = 16 * NG; // ext grid / buffer stride (u32)

                let mut base_flat = vec![0u32; base_field_inputs.len() * U * bs];
                let mut ext_flat = vec![0u32; ext_field_inputs.len() * U * es];
                let mut form_flat = vec![0u32; forms.len() * U * bs];
                let mut lazy = vec![0u64; U * es];
                let mut reduced = vec![0u32; U * es];
                let mut lazy_out = vec![0u32; es];
                let mut acc_soa = vec![0u32; es];
                let mut ext_tmp = vec![BabyBearExt4::ZERO; 4 * NG];
                let bptr = base_flat.as_mut_ptr();
                let xptr = ext_flat.as_mut_ptr();
                let fptr = form_flat.as_mut_ptr();
                let lptr = lazy.as_mut_ptr();
                let rptr = reduced.as_mut_ptr();

                let mut block = chunk_start;
                while block < chunk_start + chunk_size {
                    // STEP 1 (prover): materialize each base column's packed
                    // poly in evaluation form on all 16 points -- the 8 H
                    // values are the column's contiguous taps verbatim, the 8
                    // coset values come from the in-register LDE. (Window-3
                    // mode instead reads the 8 binary cells + extrapolates
                    // the 19 infinity cells.)
                    if mask & PH_FILL_BASE != 0 {
                        for (i, src) in base_field_inputs.iter().enumerate() {
                            let src_ptr = src.ptr as *const u32;
                            for u in 0..U {
                                let g = bptr.add((i * U + u) * bs);
                                match tables {
                                    None => lsb_read_base_w3(g, src_ptr, block + u, base_interp[i]),
                                    Some(t) => fill_base_uniskip(g, src_ptr, block + u, t),
                                }
                            }
                        }
                    }
                    // STEP 2: same for ext columns (limb-major transpose
                    // first, then one LDE per limb -- twiddles are base-field,
                    // so the transform acts limb-wise).
                    if mask & PH_FILL_EXT != 0 {
                        for (i, src) in ext_field_inputs.iter().enumerate() {
                            let src_ptr = src.ptr as *const u32;
                            for u in 0..U {
                                let g = xptr.add((i * U + u) * es);
                                match tables {
                                    None => fill_ext_w3_soa(
                                        g,
                                        src_ptr as *const BabyBearExt4,
                                        block + u,
                                        ext_interp[i],
                                        ext_tmp.as_mut_ptr(),
                                    ),
                                    Some(t) => fill_ext_uniskip_soa(g, src_ptr, block + u, t),
                                }
                            }
                        }
                    }
                    // STEP 3: materialize the bracket forms (CSE'd linear
                    // combinations shared by several products). The LDE is
                    // linear, so combining the members' full 16-cell grids is
                    // valid on the coset half too.
                    if mask & PH_FORMS != 0 {
                        for (f, members) in forms.iter().enumerate() {
                            for u in 0..U {
                                let g = fptr.add((f * U + u) * bs);
                                core::ptr::write_bytes(g, 0, bs);
                                for (op, idx) in members.iter() {
                                    apply_form_op::<F, NG>(
                                        g,
                                        bptr.add((*idx as usize * U + u) * bs),
                                        op,
                                    );
                                }
                            }
                        }
                    }

                    // STEP 4: evaluate the gate polynomial G at all 16 (or
                    // 28) points simultaneously, one term at a time, cellwise
                    // over the resident grids. base*base terms defer ALL
                    // reduction (raw u64 lane accumulation); mixed/ext terms
                    // go through the reduced SoA ext-mul path.
                    let mut lazy_products = 0usize;
                    macro_rules! lazy_tick {
                        () => {
                            lazy_products += 1;
                            if lazy_products == 2 {
                                for u in 0..U {
                                    neon::soa_lazy_condsub::<NG>(lptr.add(u * es));
                                }
                                lazy_products = 0;
                            }
                        };
                    }
                    if mask & PH_LAZY != 0 {
                        for (a, f, c) in products.iter() {
                            for u in 0..U {
                                neon::soa_quad_bb_lazy::<NG>(
                                    lptr.add(u * es),
                                    bptr.add((*a as usize * U + u) * bs),
                                    fptr.add((*f as usize * U + u) * bs),
                                    ec(c),
                                );
                            }
                            lazy_tick!();
                        }
                    }
                    for step in rest_steps.iter() {
                        match step {
                            ProgramStep::QuadBB { a, b, c } => {
                                if mask & PH_LAZY != 0 {
                                    for u in 0..U {
                                        neon::soa_quad_bb_lazy::<NG>(
                                            lptr.add(u * es),
                                            bptr.add((*a as usize * U + u) * bs),
                                            bptr.add((*b as usize * U + u) * bs),
                                            ec(c),
                                        );
                                    }
                                    lazy_tick!();
                                }
                            }
                            ProgramStep::LinB { i, c } => {
                                if mask & PH_LAZY != 0 {
                                    for u in 0..U {
                                        neon::soa_lin_base_all_n::<NBIN>(
                                            lptr.add(u * es),
                                            bptr.add((*i as usize * U + u) * bs),
                                            ec(c),
                                        );
                                    }
                                    lazy_tick!();
                                }
                            }
                            ProgramStep::QuadBE { base, ext, c } => {
                                if mask & PH_EXT != 0 {
                                    let cb = neon::soa_broadcast_ext(ec(c));
                                    for u in 0..U {
                                        neon::soa_quad_be::<NG>(
                                            rptr.add(u * es),
                                            xptr.add((*ext as usize * U + u) * es),
                                            bptr.add((*base as usize * U + u) * bs),
                                            &cb,
                                            r11v,
                                        );
                                    }
                                }
                            }
                            ProgramStep::QuadEE { a, b, c } => {
                                if mask & PH_EXT != 0 {
                                    let cb = neon::soa_broadcast_ext(ec(c));
                                    for u in 0..U {
                                        neon::soa_quad_ee_n::<NG>(
                                            rptr.add(u * es),
                                            xptr.add((*a as usize * U + u) * es),
                                            xptr.add((*b as usize * U + u) * es),
                                            &cb,
                                            r11v,
                                        );
                                    }
                                }
                            }
                            ProgramStep::LinE { i, c } => {
                                if mask & PH_EXT != 0 {
                                    let cb = neon::soa_broadcast_ext(ec(c));
                                    for u in 0..U {
                                        neon::soa_lin_ext_all_n::<NBIN>(
                                            rptr.add(u * es),
                                            xptr.add((*i as usize * U + u) * es),
                                            &cb,
                                            r11v,
                                        );
                                    }
                                }
                            }
                        }
                    }
                    if has_const && mask & PH_EXT != 0 {
                        for u in 0..U {
                            neon::soa_add_const_all_n::<NBIN>(rptr.add(u * es), &const_bcast);
                        }
                    }
                    // STEP 5 (the only place eq appears): one REDC of the
                    // lazy accumulator, then the row's G-values are scaled by
                    // the SCALAR suffix weight T(row) and added into the
                    // running accumulator. The window part of eq is applied
                    // later, to the 8 H-values of the final q when the claim
                    // is formed -- never inside this loop.
                    if mask & PH_EQ != 0 {
                        for u in 0..U {
                            neon::soa_lazy_finalize::<NG>(lptr.add(u * es), lazy_out.as_mut_ptr());
                            let eqb = neon::soa_broadcast_ext(ec(&t_suffix[block + u]));
                            neon::soa_apply_eq_and_accumulate::<NG>(
                                acc_soa.as_mut_ptr(),
                                lazy_out.as_ptr(),
                                rptr.add(u * es),
                                &eqb,
                                r11v,
                            );
                        }
                    } else {
                        // keep partial-phase work observable for the split runs
                        std::hint::black_box(&base_flat);
                        std::hint::black_box(&ext_flat);
                        std::hint::black_box(&reduced);
                        std::hint::black_box(&lazy);
                    }
                    block += U;
                }

                neon::soa_untranspose_to_aos_ext::<NG>(acc_soa.as_ptr(), ext_tmp.as_mut_ptr());
                let mut out = [E::ZERO; OUT];
                for i in 0..OUT {
                    out[i] = *(ext_tmp.as_ptr().add(i) as *const E);
                }
                *acc_dst = out;
            })
        }
    });

    reduce_chunks!(acc_chunks, OUT)
}

/// Bounded zero-reload LSB evaluator (tiled schedule with member-resident
/// forms) over the SoA engine. Window-3 loads always interpolate.
pub fn lsb_soa_bounded_parallel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const NG: usize,
    const NBIN: usize,
    const OUT: usize,
>(
    base_field_inputs: &[DisjointAccessQuasiSlice<F, false>],
    ext_field_inputs: &[DisjointAccessQuasiSlice<E, false>],
    tables: Option<&LsbLdeAny>,
    forms: &[Vec<(FormOp<F>, u16)>],
    schedule: &[TiledStep<E>],
    base_cap: usize,
    ext_cap: usize,
    additive_constant: &E,
    t_suffix: &[E],
    rows: usize,
    worker: &Worker,
) -> [E; OUT] {
    use crate::gkr::PAR_THRESHOLD;

    if const { !neon::is_bb_pair::<F, E>() } {
        unreachable!("LSB variant is BabyBear/Ext4-specific");
    }
    assert_eq!(t_suffix.len(), rows);
    let geometry = worker.get_geometry_with_threshold(rows, PAR_THRESHOLD);
    let mut acc_chunks = vec![[E::ZERO; OUT]; geometry.num_chunks];

    worker.scope_with_threshold(rows, PAR_THRESHOLD, |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let base_field_inputs = base_field_inputs.to_vec();
            let ext_field_inputs = ext_field_inputs.to_vec();
            let acc_dst = it.next().unwrap();

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                let ec = |c: &E| -> &BabyBearExt4 { &*(c as *const E as *const _) };
                let r11v = neon::soa_r11v();
                let const_bcast = neon::soa_broadcast_ext(ec(additive_constant));
                let has_const = !additive_constant.is_zero();
                let bs = 4 * NG;
                let es = 16 * NG;

                let mut base_slots = vec![0u32; base_cap * bs];
                let mut ext_slots = vec![0u32; ext_cap * es];
                let mut lazy = vec![0u64; es];
                let mut reduced = vec![0u32; es];
                let mut lazy_out = vec![0u32; es];
                let mut acc_soa = vec![0u32; es];
                let mut ext_tmp = vec![BabyBearExt4::ZERO; 4 * NG];
                let sptr = base_slots.as_mut_ptr();
                let septr = ext_slots.as_mut_ptr();

                for row in chunk_start..(chunk_start + chunk_size) {
                    let mut lazy_products = 0usize;
                    macro_rules! lazy_tick {
                        () => {
                            lazy_products += 1;
                            if lazy_products == 2 {
                                neon::soa_lazy_condsub::<NG>(lazy.as_mut_ptr());
                                lazy_products = 0;
                            }
                        };
                    }
                    for step in schedule.iter() {
                        match step {
                            TiledStep::LoadBase { slot, idx } => {
                                let g = sptr.add(*slot as usize * bs);
                                let src_ptr = base_field_inputs[*idx as usize].ptr as *const u32;
                                match tables {
                                    None => lsb_read_base_w3(g, src_ptr, row, true),
                                    Some(t) => fill_base_uniskip(g, src_ptr, row, t),
                                }
                            }
                            TiledStep::LoadExt { slot, idx } => {
                                let g = septr.add(*slot as usize * es);
                                let src_ptr = ext_field_inputs[*idx as usize].ptr as *const u32;
                                match tables {
                                    None => fill_ext_w3_soa(
                                        g,
                                        src_ptr as *const BabyBearExt4,
                                        row,
                                        true,
                                        ext_tmp.as_mut_ptr(),
                                    ),
                                    Some(t) => fill_ext_uniskip_soa(g, src_ptr, row, t),
                                }
                            }
                            TiledStep::BuildForm {
                                slot,
                                form,
                                member_slots,
                            } => {
                                let dst = sptr.add(*slot as usize * bs);
                                core::ptr::write_bytes(dst, 0, bs);
                                for ((op, _), ms) in
                                    forms[*form as usize].iter().zip(member_slots.iter())
                                {
                                    debug_assert_ne!(*ms, *slot);
                                    apply_form_op::<F, NG>(dst, sptr.add(*ms as usize * bs), op);
                                }
                            }
                            TiledStep::QuadBB { sa, sb, c } => {
                                neon::soa_quad_bb_lazy::<NG>(
                                    lazy.as_mut_ptr(),
                                    sptr.add(*sa as usize * bs),
                                    sptr.add(*sb as usize * bs),
                                    ec(c),
                                );
                                lazy_tick!();
                            }
                            TiledStep::QuadBE { sb, se, c } => {
                                let cb = neon::soa_broadcast_ext(ec(c));
                                neon::soa_quad_be::<NG>(
                                    reduced.as_mut_ptr(),
                                    septr.add(*se as usize * es),
                                    sptr.add(*sb as usize * bs),
                                    &cb,
                                    r11v,
                                );
                            }
                            TiledStep::QuadEE { sa, sb, c } => {
                                let cb = neon::soa_broadcast_ext(ec(c));
                                neon::soa_quad_ee_n::<NG>(
                                    reduced.as_mut_ptr(),
                                    septr.add(*sa as usize * es),
                                    septr.add(*sb as usize * es),
                                    &cb,
                                    r11v,
                                );
                            }
                            TiledStep::LinB { slot, c } => {
                                neon::soa_lin_base_all_n::<NBIN>(
                                    lazy.as_mut_ptr(),
                                    sptr.add(*slot as usize * bs),
                                    ec(c),
                                );
                                lazy_tick!();
                            }
                            TiledStep::LinE { slot, c } => {
                                let cb = neon::soa_broadcast_ext(ec(c));
                                neon::soa_lin_ext_all_n::<NBIN>(
                                    reduced.as_mut_ptr(),
                                    septr.add(*slot as usize * es),
                                    &cb,
                                    r11v,
                                );
                            }
                        }
                    }
                    if has_const {
                        neon::soa_add_const_all_n::<NBIN>(reduced.as_mut_ptr(), &const_bcast);
                    }
                    neon::soa_lazy_finalize::<NG>(lazy.as_mut_ptr(), lazy_out.as_mut_ptr());
                    let eqb = neon::soa_broadcast_ext(ec(&t_suffix[row]));
                    neon::soa_apply_eq_and_accumulate::<NG>(
                        acc_soa.as_mut_ptr(),
                        lazy_out.as_ptr(),
                        reduced.as_mut_ptr(),
                        &eqb,
                        r11v,
                    );
                }

                neon::soa_untranspose_to_aos_ext::<NG>(acc_soa.as_ptr(), ext_tmp.as_mut_ptr());
                let mut out = [E::ZERO; OUT];
                for i in 0..OUT {
                    out[i] = *(ext_tmp.as_ptr().add(i) as *const E);
                }
                *acc_dst = out;
            })
        }
    });

    reduce_chunks!(acc_chunks, OUT)
}

/// Ext-only uniskip pass for the folded stages of the LSB chain: every poly is
/// an ext column, forms are built in ext SoA from the folded grids, and all
/// terms run through the SoA ext-mul path into the `reduced` scratch (no lazy
/// u64 -- there are no base*base products left). `quads`/`lins` index the
/// combined folded slot space (base-origin polys first). Returns the 16-point
/// packed q accumulator.
pub fn lsb_uniskip_ext_pass_parallel<
    F: PrimeField,
    E: FieldExtension<F> + Field,
    const U: usize,
>(
    ext_inputs: &[DisjointAccessQuasiSlice<E, false>],
    forms: &[Vec<(FormOp<F>, u16)>],
    products: &[(u16, u16, E)],
    quads: &[(u16, u16, E)],
    lins: &[(u16, E)],
    additive_constant: &E,
    tables: &LsbLdeAny,
    t_suffix: &[E],
    rows: usize,
    worker: &Worker,
) -> [E; 16] {
    use crate::gkr::PAR_THRESHOLD;

    if const { !neon::is_bb_pair::<F, E>() } {
        unreachable!("LSB variant is BabyBear/Ext4-specific");
    }
    assert_eq!(t_suffix.len(), rows);
    assert_eq!(rows % U, 0);
    let num_blocks = rows / U;
    let geometry = worker.get_geometry_with_threshold(num_blocks, (PAR_THRESHOLD / U).max(1));
    let mut acc_chunks = vec![[E::ZERO; 16]; geometry.num_chunks];

    worker.scope_with_threshold(num_blocks, (PAR_THRESHOLD / U).max(1), |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx) * U;
            let chunk_size = geometry.get_chunk_size(thread_idx) * U;
            let ext_inputs = ext_inputs.to_vec();
            let acc_dst = it.next().unwrap();

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                let ec = |c: &E| -> &BabyBearExt4 { &*(c as *const E as *const _) };
                let r11v = neon::soa_r11v();
                let const_bcast = neon::soa_broadcast_ext(ec(additive_constant));
                let has_const = !additive_constant.is_zero();
                const NG: usize = 4;
                let es = 16 * NG;

                let mut ext_flat = vec![0u32; ext_inputs.len() * U * es];
                let mut form_flat = vec![0u32; forms.len() * U * es];
                let mut lazy = vec![0u64; U * es];
                let mut lazy_out = vec![0u32; es];
                let mut acc_soa = vec![0u32; es];
                let mut ext_tmp = vec![BabyBearExt4::ZERO; 4 * NG];
                let xptr = ext_flat.as_mut_ptr();
                let fptr = form_flat.as_mut_ptr();
                let lptr = lazy.as_mut_ptr();
                // per-term coefficient tables (canonical entries, lazy-accumulable)
                let tab = |c: &E| neon::SoaExtTable::new(ec(c));
                let tables_p: Vec<neon::SoaExtTable> =
                    products.iter().map(|(_, _, c)| tab(c)).collect();
                let tables_q: Vec<neon::SoaExtTable> =
                    quads.iter().map(|(_, _, c)| tab(c)).collect();
                let tables_l: Vec<neon::SoaExtTable> = lins.iter().map(|(_, c)| tab(c)).collect();

                let mut block = chunk_start;
                while block < chunk_start + chunk_size {
                    for (i, src) in ext_inputs.iter().enumerate() {
                        let src_ptr = src.ptr as *const u32;
                        for u in 0..U {
                            fill_ext_uniskip_soa(
                                xptr.add((i * U + u) * es),
                                src_ptr,
                                block + u,
                                tables,
                            );
                        }
                    }
                    for (f, members) in forms.iter().enumerate() {
                        for u in 0..U {
                            let g = fptr.add((f * U + u) * es);
                            core::ptr::write_bytes(g, 0, es);
                            for (op, idx) in members.iter() {
                                let src = xptr.add((*idx as usize * U + u) * es);
                                match op {
                                    FormOp::Add => neon::soa_ext_form_add_n::<NG>(g, src),
                                    FormOp::Sub => neon::soa_ext_form_sub_n::<NG>(g, src),
                                    FormOp::Mul(c) => neon::soa_ext_form_muladd_n::<NG>(
                                        g,
                                        src,
                                        *(c as *const F as *const _),
                                    ),
                                }
                            }
                        }
                    }
                    for ((a, f, _), tb) in products.iter().zip(tables_p.iter()) {
                        for u in 0..U {
                            neon::soa_quad_ee_lazy::<NG>(
                                lptr.add(u * es),
                                xptr.add((*a as usize * U + u) * es),
                                fptr.add((*f as usize * U + u) * es),
                                tb,
                                r11v,
                            );
                        }
                    }
                    for ((a, b, _), tb) in quads.iter().zip(tables_q.iter()) {
                        for u in 0..U {
                            neon::soa_quad_ee_lazy::<NG>(
                                lptr.add(u * es),
                                xptr.add((*a as usize * U + u) * es),
                                xptr.add((*b as usize * U + u) * es),
                                tb,
                                r11v,
                            );
                        }
                    }
                    for ((i, _), tb) in lins.iter().zip(tables_l.iter()) {
                        for u in 0..U {
                            neon::soa_lin_ext_lazy::<NG>(
                                lptr.add(u * es),
                                xptr.add((*i as usize * U + u) * es),
                                tb,
                            );
                        }
                    }
                    for u in 0..U {
                        neon::soa_lazy_finalize::<NG>(lptr.add(u * es), lazy_out.as_mut_ptr());
                        if has_const {
                            // add in canonical (Montgomery) domain AFTER the
                            // REDC -- the lazy accumulator holds R^2-scaled sums
                            neon::soa_add_const_all_n::<NG>(lazy_out.as_mut_ptr(), &const_bcast);
                        }
                        let eqb = neon::soa_broadcast_ext(ec(&t_suffix[block + u]));
                        neon::soa_apply_eq_and_accumulate_n::<NG>(
                            acc_soa.as_mut_ptr(),
                            lazy_out.as_mut_ptr(),
                            &eqb,
                            r11v,
                        );
                    }
                    block += U;
                }

                neon::soa_untranspose_to_aos_ext::<NG>(acc_soa.as_ptr(), ext_tmp.as_mut_ptr());
                let mut out = [E::ZERO; 16];
                for i in 0..16 {
                    out[i] = *(ext_tmp.as_ptr().add(i) as *const E);
                }
                *acc_dst = out;
            })
        }
    });

    reduce_chunks!(acc_chunks, 16)
}

/// Lagrange fold of a base column in LSB layout: `dst[row] = sum_j w_j *
/// src[8*row + j]` (packed-poly evaluation at the challenge).
pub fn lsb_fold_base_parallel<F: PrimeField, E: FieldExtension<F> + Field>(
    src_ptr: *const u8,
    dst: &mut [E],
    weights: &[E; 8],
    worker: &Worker,
) {
    use crate::gkr::PAR_THRESHOLD;
    use core::arch::aarch64::vdupq_n_u32;

    if const { !neon::is_bb_pair::<F, E>() } {
        unreachable!("LSB variant is BabyBear/Ext4-specific");
    }
    let rows = dst.len();
    let dst_addr = dst.as_mut_ptr() as usize;
    let src_addr = src_ptr as usize;
    worker.scope_with_threshold(rows, PAR_THRESHOLD, |scope, geometry| {
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                let w: [uint32x4_t; 8] =
                    core::array::from_fn(|j| vld1q_u32(&weights[j] as *const E as *const u32));
                let sp = src_addr as *const u32;
                let dp = dst_addr as *mut BabyBearExt4;
                for row in chunk_start..(chunk_start + chunk_size) {
                    let taps = sp.add(row * 8);
                    let mut acc = neon::mont_mul4(w[0], vdupq_n_u32(*taps));
                    for j in 1..8 {
                        acc = neon::add4(acc, neon::mont_mul4(w[j], vdupq_n_u32(*taps.add(j))));
                    }
                    vst1q_u32(dp.add(row) as *mut u32, acc);
                }
            })
        }
    });
}

/// Lagrange fold of an ext column in LSB layout: `dst[row] = sum_j w_j (x)
/// src[8*row + j]`.
pub fn lsb_fold_ext_parallel<E: Field>(
    src_ptr: *const u8,
    dst: &mut [E],
    weights: &[E; 8],
    worker: &Worker,
) {
    use crate::gkr::PAR_THRESHOLD;

    if const { !neon::is_bb4::<E>() } {
        unreachable!("LSB variant is BabyBear/Ext4-specific");
    }
    let rows = dst.len();
    let dst_addr = dst.as_mut_ptr() as usize;
    let src_addr = src_ptr as usize;
    worker.scope_with_threshold(rows, PAR_THRESHOLD, |scope, geometry| {
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                let tables: [neon::ExtMatrix; 8] = core::array::from_fn(|j| {
                    neon::ExtMatrix::new(&*(&weights[j] as *const E as *const BabyBearExt4))
                });
                let sp = src_addr as *const BabyBearExt4;
                let dp = dst_addr as *mut BabyBearExt4;
                for row in chunk_start..(chunk_start + chunk_size) {
                    let taps = sp.add(row * 8);
                    let mut acc = neon::mat_mul(&tables[0], vld1q_u32(taps as *const u32));
                    for j in 1..8 {
                        acc = neon::add4(
                            acc,
                            neon::mat_mul(&tables[j], vld1q_u32(taps.add(j) as *const u32)),
                        );
                    }
                    vst1q_u32(dp.add(row) as *mut u32, acc);
                }
            })
        }
    });
}

/// SoA variant of [`lsb_fold_base_parallel`]: 4 output rows per call, taps
/// transposed in-register, lazy u64 accumulation (requires `dst.len() % 4 == 0`).
pub fn lsb_fold_base_soa_parallel<F: PrimeField, E: FieldExtension<F> + Field>(
    src_ptr: *const u8,
    dst: &mut [E],
    weights: &[E; 8],
    worker: &Worker,
) {
    use crate::gkr::PAR_THRESHOLD;
    use core::arch::aarch64::vdupq_n_u32;

    if const { !neon::is_bb_pair::<F, E>() } {
        unreachable!("LSB variant is BabyBear/Ext4-specific");
    }
    let rows = dst.len();
    assert_eq!(rows % 4, 0);
    let blocks = rows / 4;
    let dst_addr = dst.as_mut_ptr() as usize;
    let src_addr = src_ptr as usize;
    worker.scope_with_threshold(blocks, (PAR_THRESHOLD / 4).max(1), |scope, geometry| {
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                let prefix_limbs: [[uint32x4_t; 4]; 8] = core::array::from_fn(|i| {
                    let limbs: [u32; 4] =
                        core::mem::transmute(*(&weights[i] as *const E as *const BabyBearExt4));
                    core::array::from_fn(|l| vdupq_n_u32(limbs[l]))
                });
                let sp = src_addr as *const _;
                let dp = dst_addr as *mut BabyBearExt4;
                for blk in chunk_start..(chunk_start + chunk_size) {
                    let limbs = neon::lsb_soa_fold8_base(sp, &prefix_limbs, blk);
                    neon::soa_store_ext4(&limbs, dp.add(4 * blk));
                }
            })
        }
    });
}

/// SoA variant of [`lsb_fold_ext_parallel`]: 4 output rows per call, per-tap
/// strided transpose + canonical `SoaExtTable` lazy accumulation.
pub fn lsb_fold_ext_soa_parallel<E: Field>(
    src_ptr: *const u8,
    dst: &mut [E],
    weights: &[E; 8],
    worker: &Worker,
) {
    use crate::gkr::PAR_THRESHOLD;

    if const { !neon::is_bb4::<E>() } {
        unreachable!("LSB variant is BabyBear/Ext4-specific");
    }
    let rows = dst.len();
    assert_eq!(rows % 4, 0);
    let blocks = rows / 4;
    let dst_addr = dst.as_mut_ptr() as usize;
    let src_addr = src_ptr as usize;
    worker.scope_with_threshold(blocks, (PAR_THRESHOLD / 4).max(1), |scope, geometry| {
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                let tables: [neon::SoaExtTable; 8] = core::array::from_fn(|i| {
                    neon::SoaExtTable::new(&*(&weights[i] as *const E as *const BabyBearExt4))
                });
                let sp = src_addr as *const BabyBearExt4;
                let dp = dst_addr as *mut BabyBearExt4;
                for blk in chunk_start..(chunk_start + chunk_size) {
                    let limbs = neon::lsb_soa_fold8_ext(sp, &tables, blk);
                    neon::soa_store_ext4(&limbs, dp.add(4 * blk));
                }
            })
        }
    });
}

/// Fused pass-0 fold + pass-1 evaluation: for each pass-1 row, the 8 folded
/// values per poly are produced straight from the 64 contiguous (and cache-
/// hot) pass-0 taps via the SoA fold kernels -- their limb-major output IS
/// the uniskip grid's H-half layout, so they are stored into the local grid,
/// untransposed once into the global folding buffer (for pass 2), LDE'd
/// per limb, and immediately consumed by the lazy term program. Saves the
/// full re-read of the folded columns that a separate pass-1 would do.
pub fn lsb_fold_and_ext_pass_parallel<F: PrimeField, E: FieldExtension<F> + Field>(
    base_srcs: &[usize], // pass-0 base column ptrs (LSB-ordered data)
    ext_srcs: &[usize],  // pass-0 ext column ptrs
    fold_out: &[usize],  // nb+ne folded column ptrs (each 8 * rows ext values)
    fold_w: &[E; 8],
    forms: &[Vec<(FormOp<F>, u16)>],
    products: &[(u16, u16, E)],
    quads: &[(u16, u16, E)],
    lins: &[(u16, E)],
    additive_constant: &E,
    tables: &LsbLdeAny,
    t_suffix: &[E], // len = pass-1 rows
    worker: &Worker,
) -> [E; 16] {
    use crate::gkr::PAR_THRESHOLD;
    use core::arch::aarch64::vdupq_n_u32;

    if const { !neon::is_bb_pair::<F, E>() } {
        unreachable!("LSB variant is BabyBear/Ext4-specific");
    }
    let rows = t_suffix.len();
    let nb = base_srcs.len();
    let ne = ext_srcs.len();
    assert_eq!(fold_out.len(), nb + ne);
    let geometry = worker.get_geometry_with_threshold(rows, (PAR_THRESHOLD / 8).max(1));
    let mut acc_chunks = vec![[E::ZERO; 16]; geometry.num_chunks];

    worker.scope_with_threshold(rows, (PAR_THRESHOLD / 8).max(1), |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let base_srcs = base_srcs.to_vec();
            let ext_srcs = ext_srcs.to_vec();
            let fold_out = fold_out.to_vec();
            let acc_dst = it.next().unwrap();

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                let ec = |c: &E| -> &BabyBearExt4 { &*(c as *const E as *const _) };
                let r11v = neon::soa_r11v();
                let const_bcast = neon::soa_broadcast_ext(ec(additive_constant));
                let has_const = !additive_constant.is_zero();
                const NG: usize = 4;
                let es = 16 * NG;

                // fold weight forms
                let prefix_limbs: [[uint32x4_t; 4]; 8] = core::array::from_fn(|i| {
                    let limbs: [u32; 4] =
                        core::mem::transmute(*(&fold_w[i] as *const E as *const BabyBearExt4));
                    core::array::from_fn(|l| vdupq_n_u32(limbs[l]))
                });
                let fold_tables: [neon::SoaExtTable; 8] = core::array::from_fn(|i| {
                    neon::SoaExtTable::new(&*(&fold_w[i] as *const E as *const BabyBearExt4))
                });
                // per-term coefficient tables
                let tab = |c: &E| neon::SoaExtTable::new(ec(c));
                let tables_p: Vec<neon::SoaExtTable> =
                    products.iter().map(|(_, _, c)| tab(c)).collect();
                let tables_q: Vec<neon::SoaExtTable> =
                    quads.iter().map(|(_, _, c)| tab(c)).collect();
                let tables_l: Vec<neon::SoaExtTable> = lins.iter().map(|(_, c)| tab(c)).collect();

                let mut ext_flat = vec![0u32; (nb + ne) * es];
                let mut form_flat = vec![0u32; forms.len() * es];
                let mut lazy = vec![0u64; es];
                let mut lazy_out = vec![0u32; es];
                let mut acc_soa = vec![0u32; es];
                let mut ext_tmp = vec![BabyBearExt4::ZERO; 4 * NG];
                let xptr = ext_flat.as_mut_ptr();
                let fptr = form_flat.as_mut_ptr();
                let lptr = lazy.as_mut_ptr();

                let lde = |grid: *mut u32| {
                    // per-limb coset half from the H half already in the grid
                    match tables {
                        LsbLdeAny::K8Mat(bt) => {
                            for l in 0..4 {
                                let h =
                                    [vld1q_u32(grid.add(4 * l)), vld1q_u32(grid.add(16 + 4 * l))];
                                let coset = neon::lsb_lde8_base_mat(h, bt);
                                vst1q_u32(grid.add(32 + 4 * l), coset[0]);
                                vst1q_u32(grid.add(48 + 4 * l), coset[1]);
                            }
                        }
                        LsbLdeAny::K8(bt) => {
                            for l in 0..4 {
                                let h =
                                    [vld1q_u32(grid.add(4 * l)), vld1q_u32(grid.add(16 + 4 * l))];
                                let coset = neon::lsb_lde8_base_lazy(h, bt);
                                vst1q_u32(grid.add(32 + 4 * l), coset[0]);
                                vst1q_u32(grid.add(48 + 4 * l), coset[1]);
                            }
                        }
                        LsbLdeAny::K64(_) => unreachable!("fused pass is k=3 only"),
                    }
                };

                for row in chunk_start..(chunk_start + chunk_size) {
                    // fold 8 values per poly from the 64 hot pass-0 taps,
                    // store to grid H half + global folding buffer, then LDE
                    for i in 0..nb {
                        let grid = xptr.add(i * es);
                        let sp = base_srcs[i] as *const _;
                        let g0 = neon::lsb_soa_fold8_base(sp, &prefix_limbs, 2 * row);
                        let g1 = neon::lsb_soa_fold8_base(sp, &prefix_limbs, 2 * row + 1);
                        neon::soa_store_cell(grid, &g0);
                        neon::soa_store_cell(grid.add(16), &g1);
                        let out = fold_out[i] as *mut BabyBearExt4;
                        neon::soa_store_ext4(&g0, out.add(8 * row));
                        neon::soa_store_ext4(&g1, out.add(8 * row + 4));
                        lde(grid);
                    }
                    for i in 0..ne {
                        let grid = xptr.add((nb + i) * es);
                        let sp = ext_srcs[i] as *const BabyBearExt4;
                        let g0 = neon::lsb_soa_fold8_ext(sp, &fold_tables, 2 * row);
                        let g1 = neon::lsb_soa_fold8_ext(sp, &fold_tables, 2 * row + 1);
                        neon::soa_store_cell(grid, &g0);
                        neon::soa_store_cell(grid.add(16), &g1);
                        let out = fold_out[nb + i] as *mut BabyBearExt4;
                        neon::soa_store_ext4(&g0, out.add(8 * row));
                        neon::soa_store_ext4(&g1, out.add(8 * row + 4));
                        lde(grid);
                    }
                    for (f, members) in forms.iter().enumerate() {
                        let g = fptr.add(f * es);
                        core::ptr::write_bytes(g, 0, es);
                        for (op, idx) in members.iter() {
                            let src = xptr.add(*idx as usize * es);
                            match op {
                                FormOp::Add => neon::soa_ext_form_add_n::<NG>(g, src),
                                FormOp::Sub => neon::soa_ext_form_sub_n::<NG>(g, src),
                                FormOp::Mul(c) => neon::soa_ext_form_muladd_n::<NG>(
                                    g,
                                    src,
                                    *(c as *const F as *const _),
                                ),
                            }
                        }
                    }
                    for ((a, f, _), tb) in products.iter().zip(tables_p.iter()) {
                        neon::soa_quad_ee_lazy::<NG>(
                            lptr,
                            xptr.add(*a as usize * es),
                            fptr.add(*f as usize * es),
                            tb,
                            r11v,
                        );
                    }
                    for ((a, b, _), tb) in quads.iter().zip(tables_q.iter()) {
                        neon::soa_quad_ee_lazy::<NG>(
                            lptr,
                            xptr.add(*a as usize * es),
                            xptr.add(*b as usize * es),
                            tb,
                            r11v,
                        );
                    }
                    for ((i, _), tb) in lins.iter().zip(tables_l.iter()) {
                        neon::soa_lin_ext_lazy::<NG>(lptr, xptr.add(*i as usize * es), tb);
                    }
                    neon::soa_lazy_finalize::<NG>(lptr, lazy_out.as_mut_ptr());
                    if has_const {
                        neon::soa_add_const_all_n::<NG>(lazy_out.as_mut_ptr(), &const_bcast);
                    }
                    let eqb = neon::soa_broadcast_ext(ec(&t_suffix[row]));
                    neon::soa_apply_eq_and_accumulate_n::<NG>(
                        acc_soa.as_mut_ptr(),
                        lazy_out.as_mut_ptr(),
                        &eqb,
                        r11v,
                    );
                }

                neon::soa_untranspose_to_aos_ext::<NG>(acc_soa.as_ptr(), ext_tmp.as_mut_ptr());
                let mut out = [E::ZERO; 16];
                for i in 0..16 {
                    out[i] = *(ext_tmp.as_ptr().add(i) as *const E);
                }
                *acc_dst = out;
            })
        }
    });

    reduce_chunks!(acc_chunks, 16)
}
