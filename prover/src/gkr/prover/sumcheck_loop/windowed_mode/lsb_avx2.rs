//! AVX2 twin of the PRODUCTION window-3 subset of `lsb_bench`: the SoA
//! window passes (initial over the layer's base/ext columns, continuing over
//! the folded ext tables) and the 8-tap folds, for the LSB-binding same-size
//! chain on BabyBear/Ext4.
//!
//! Grid layout (8 CELLS per vector): the 27-cell `{0,1,inf}^3` window grid is
//! padded to `NG = 4` groups of 8 cells; the binary cells 0..8 (natural tap
//! order `b = 4*x0 + 2*x1 + x2`) fill group 0 (`NBIN = 1`), the 19 infinity
//! extrapolations live at cells 8..27 per [`W3_INF`], cells 27..32 are
//! padding (zero, never read out). Base grids are `[NG][8]` u32, ext grids /
//! scratch `[NG][4 limbs][8]` u32, the lazy accumulator `[NG][4 limbs][8]`
//! u64. Everything else — the per-row steps, the mixed-degree form-constant
//! rule (constants hit the real evaluation cells only), the lazy cadence —
//! mirrors the NEON kernels, so the accumulators are byte-identical (the
//! chain executor permutes the SoA cell order into the generic 27-cell order
//! through [`w3_soa_cell_of_generic`]).

use super::avx2;
use super::program::{FormDesc, FormOp, FormRef, ProgramStep};
use crate::gkr::sumcheck::access_and_fold::DisjointAccessQuasiSlice;
use crate::worker::Worker;
use ::field::baby_bear::base::BabyBearField;
use ::field::baby_bear::ext4::BabyBearExt4;
use ::field::Field;

pub(crate) const NG: usize = 4;
pub(crate) const NBIN: usize = 1;
pub(crate) const OUT: usize = 27;
const BS: usize = 8 * NG;
const ES: usize = 32 * NG;

const P: u32 = 0x78000001;

/// (dst, hi, lo): cell `dst` = cell `hi` - cell `lo`, in dependency order.
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

/// SoA cell index of the GENERIC-layout `{0,1,inf}^3` cell
/// `g = 9*c0 + 3*c1 + c2` (c0 bound first, 2 = inf) — identical to the NEON
/// layout, so the same permutation hands the driver the generic order.
#[inline(always)]
pub(crate) fn w3_soa_cell_of_generic(g: usize) -> usize {
    let (c0, c1, c2) = (g / 9, (g / 3) % 3, g % 3);
    if c0 < 2 && c1 < 2 && c2 < 2 {
        c0 + 2 * c1 + 4 * c2
    } else if c0 == 2 && c1 < 2 && c2 < 2 {
        8 + 2 * c2 + c1
    } else if c1 == 2 && c2 < 2 {
        12 + 3 * c2 + c0
    } else {
        18 + 3 * c1 + c0
    }
}

#[inline(always)]
unsafe fn lsb_read_base_w3(dst: *mut u32, src: *const u32, row: usize, interpolate: bool) {
    avx2::st(dst, avx2::ld(src.add(row * 8)));
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

/// window-3 ext fill: AoS read + extrapolation into `tmp` (32 cells), then
/// limb-major transpose into the 4-group SoA grid.
#[inline(always)]
unsafe fn fill_ext_w3_soa(
    grid: *mut u32,
    src: *const BabyBearExt4,
    row: usize,
    interpolate: bool,
    tmp: *mut BabyBearExt4,
) {
    lsb_read_ext_w3_aos(tmp, src, row, interpolate);
    for g in 0..NG {
        let t = avx2::soa_transpose_ext8(tmp.add(8 * g));
        avx2::soa_store_cell(grid.add(32 * g), &t);
    }
}

#[inline(always)]
unsafe fn apply_form_op(dst: *mut u32, src: *const u32, op: &FormOp<BabyBearField>) {
    match op {
        FormOp::Add => avx2::soa_base_form_add_n::<NG>(dst, src),
        FormOp::Sub => avx2::soa_base_form_sub_n::<NG>(dst, src),
        FormOp::Mul(c) => avx2::soa_base_form_muladd_n::<NG>(dst, src, *c),
    }
}
#[inline(always)]
unsafe fn apply_form_op_first(dst: *mut u32, src: *const u32, op: &FormOp<BabyBearField>) {
    match op {
        FormOp::Add => avx2::soa_base_form_store_n::<NG>(dst, src),
        FormOp::Sub => avx2::soa_base_form_neg_store_n::<NG>(dst, src),
        FormOp::Mul(c) => avx2::soa_base_form_mul_store_n::<NG>(dst, src, *c),
    }
}
#[inline(always)]
unsafe fn apply_ext_form_op(dst: *mut u32, src: *const u32, op: &FormOp<BabyBearField>) {
    match op {
        FormOp::Add => avx2::soa_ext_form_add_n::<NG>(dst, src),
        FormOp::Sub => avx2::soa_ext_form_sub_n::<NG>(dst, src),
        FormOp::Mul(c) => avx2::soa_ext_form_muladd_n::<NG>(dst, src, *c),
    }
}
#[inline(always)]
unsafe fn apply_ext_form_op_first(dst: *mut u32, src: *const u32, op: &FormOp<BabyBearField>) {
    match op {
        FormOp::Add => avx2::soa_ext_form_store_n::<NG>(dst, src),
        FormOp::Sub => avx2::soa_ext_form_neg_store_n::<NG>(dst, src),
        FormOp::Mul(c) => avx2::soa_ext_form_mul_store_n::<NG>(dst, src, *c),
    }
}

/// Untranspose the SoA chunk accumulator into AoS ext values and read out the
/// first `OUT` cells.
#[inline(always)]
unsafe fn finish_soa_acc(acc_soa: &[u32], ext_tmp: &mut [BabyBearExt4]) -> [BabyBearExt4; OUT] {
    avx2::soa_untranspose_to_aos_ext::<NG>(acc_soa.as_ptr(), ext_tmp.as_mut_ptr());
    let mut out = [BabyBearExt4::ZERO; OUT];
    out.copy_from_slice(&ext_tmp[..OUT]);
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

/// INITIAL window-3 pass over the layer's original base/ext columns: per row
/// (8 contiguous taps per column) build the 27-cell grids (difference
/// extension per slot flag), materialize the bracket forms, evaluate the
/// gate polynomial cellwise (base*base products and base linear terms lazily
/// in u64, mixed/ext terms through the reduced path), weight by the scalar
/// suffix-eq factor and accumulate. `U` unrolls rows.
#[allow(clippy::too_many_arguments)]
pub(crate) fn lsb_soa_full_parallel_w3<const U: usize>(
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

    assert_eq!(t_suffix.len(), rows);
    assert_eq!(rows % U, 0);
    let num_blocks = rows / U;
    let geometry = worker.get_geometry_with_threshold(num_blocks, (PAR_THRESHOLD / U).max(1));
    let mut acc_chunks = vec![[BabyBearExt4::ZERO; OUT]; geometry.num_chunks];

    worker.scope_with_threshold(num_blocks, (PAR_THRESHOLD / U).max(1), |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx) * U;
            let chunk_size = geometry.get_chunk_size(thread_idx) * U;
            let base_field_inputs = base_field_inputs.to_vec();
            let ext_field_inputs = ext_field_inputs.to_vec();
            let acc_dst = it.next().unwrap();

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                let r11v = avx2::r11v();
                let const_bcast = avx2::soa_broadcast_ext(additive_constant);
                let has_const = !additive_constant.is_zero();

                let mut base_flat = vec![0u32; base_field_inputs.len() * U * BS];
                let mut ext_flat = vec![0u32; ext_field_inputs.len() * U * ES];
                let mut form_flat = vec![0u32; forms.len() * U * BS];
                let mut lazy = vec![0u64; U * ES];
                let mut reduced = vec![0u32; U * ES];
                let mut lazy_out = vec![0u32; ES];
                let mut acc_soa = vec![0u32; ES];
                let mut ext_tmp = vec![BabyBearExt4::ZERO; 8 * NG];
                let bptr = base_flat.as_mut_ptr();
                let xptr = ext_flat.as_mut_ptr();
                let fptr = form_flat.as_mut_ptr();
                let lptr = lazy.as_mut_ptr();
                let rptr = reduced.as_mut_ptr();

                let mut block = chunk_start;
                while block < chunk_start + chunk_size {
                    for (i, src) in base_field_inputs.iter().enumerate() {
                        let src_ptr = src.ptr as *const u32;
                        for u in 0..U {
                            lsb_read_base_w3(
                                bptr.add((i * U + u) * BS),
                                src_ptr,
                                block + u,
                                base_interp[i],
                            );
                        }
                    }
                    for (i, src) in ext_field_inputs.iter().enumerate() {
                        let src_ptr = src.ptr as *const BabyBearExt4;
                        for u in 0..U {
                            fill_ext_w3_soa(
                                xptr.add((i * U + u) * ES),
                                src_ptr,
                                block + u,
                                ext_interp[i],
                                ext_tmp.as_mut_ptr(),
                            );
                        }
                    }
                    for (f, form) in forms.iter().enumerate() {
                        for u in 0..U {
                            let g = fptr.add((f * U + u) * BS);
                            let mut it = form.members.iter();
                            match it.next() {
                                Some((op, idx)) => apply_form_op_first(
                                    g,
                                    bptr.add((*idx as usize * U + u) * BS),
                                    op,
                                ),
                                None => core::ptr::write_bytes(g, 0, BS),
                            }
                            for (op, idx) in it {
                                apply_form_op(g, bptr.add((*idx as usize * U + u) * BS), op);
                            }
                            if !form.constant.is_zero() {
                                avx2::soa_base_form_add_const_n::<NBIN>(g, form.constant);
                            }
                        }
                    }

                    let mut lazy_products = 0usize;
                    macro_rules! lazy_tick {
                        () => {
                            lazy_products += 1;
                            if lazy_products == 2 {
                                for u in 0..U {
                                    avx2::soa_lazy_condsub::<NG>(lptr.add(u * ES));
                                }
                                lazy_products = 0;
                            }
                        };
                    }
                    for (a, b, c) in products.iter() {
                        let pa = |u: usize| match a {
                            FormRef::Slot(i) => bptr.add((*i as usize * U + u) * BS),
                            FormRef::Form(i) => fptr.add((*i as usize * U + u) * BS),
                        };
                        let pb = |u: usize| match b {
                            FormRef::Slot(i) => bptr.add((*i as usize * U + u) * BS),
                            FormRef::Form(i) => fptr.add((*i as usize * U + u) * BS),
                        };
                        for u in 0..U {
                            avx2::soa_quad_bb_lazy::<NG>(lptr.add(u * ES), pa(u), pb(u), c);
                        }
                        lazy_tick!();
                    }
                    for step in rest_steps.iter() {
                        match step {
                            ProgramStep::QuadBB { a, b, c } => {
                                for u in 0..U {
                                    avx2::soa_quad_bb_lazy::<NG>(
                                        lptr.add(u * ES),
                                        bptr.add((*a as usize * U + u) * BS),
                                        bptr.add((*b as usize * U + u) * BS),
                                        c,
                                    );
                                }
                                lazy_tick!();
                            }
                            ProgramStep::LinB { i, c } => {
                                for u in 0..U {
                                    avx2::soa_lin_base_all_n::<NBIN>(
                                        lptr.add(u * ES),
                                        bptr.add((*i as usize * U + u) * BS),
                                        c,
                                    );
                                }
                                lazy_tick!();
                            }
                            ProgramStep::QuadBE { base, ext, c } => {
                                let cb = avx2::soa_broadcast_ext(c);
                                for u in 0..U {
                                    avx2::soa_quad_be::<NG>(
                                        rptr.add(u * ES),
                                        xptr.add((*ext as usize * U + u) * ES),
                                        bptr.add((*base as usize * U + u) * BS),
                                        &cb,
                                        r11v,
                                    );
                                }
                            }
                            ProgramStep::QuadEE { a, b, c } => {
                                let cb = avx2::soa_broadcast_ext(c);
                                for u in 0..U {
                                    avx2::soa_quad_ee_n::<NG>(
                                        rptr.add(u * ES),
                                        xptr.add((*a as usize * U + u) * ES),
                                        xptr.add((*b as usize * U + u) * ES),
                                        &cb,
                                        r11v,
                                    );
                                }
                            }
                            ProgramStep::LinE { i, c } => {
                                let cb = avx2::soa_broadcast_ext(c);
                                for u in 0..U {
                                    avx2::soa_lin_ext_all_n::<NBIN>(
                                        rptr.add(u * ES),
                                        xptr.add((*i as usize * U + u) * ES),
                                        &cb,
                                        r11v,
                                    );
                                }
                            }
                        }
                    }
                    if has_const {
                        for u in 0..U {
                            avx2::soa_add_const_all_n::<NBIN>(rptr.add(u * ES), &const_bcast);
                        }
                    }
                    for u in 0..U {
                        avx2::soa_lazy_finalize::<NG>(lptr.add(u * ES), lazy_out.as_mut_ptr());
                        let eqb = avx2::soa_broadcast_ext(&t_suffix[block + u]);
                        avx2::soa_apply_eq_and_accumulate::<NG>(
                            acc_soa.as_mut_ptr(),
                            lazy_out.as_ptr(),
                            rptr.add(u * ES),
                            &eqb,
                            r11v,
                        );
                    }
                    block += U;
                }

                *acc_dst = finish_soa_acc(&acc_soa, &mut ext_tmp);
            })
        }
    });

    reduce_chunks(acc_chunks)
}

/// CONTINUING window-3 pass over the folded (all-ext) tables: forms, factored
/// products, expanded quads and linear terms all through the lazy ext path;
/// the additive constant is added in the canonical domain after the REDC.
#[allow(clippy::too_many_arguments)]
pub(crate) fn lsb_soa_ext_pass_parallel_w3<const U: usize>(
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
    assert_eq!(rows % U, 0);
    assert_eq!(interp.len(), ext_inputs.len());
    let num_blocks = rows / U;
    let geometry = worker.get_geometry_with_threshold(num_blocks, (PAR_THRESHOLD / U).max(1));
    let mut acc_chunks = vec![[BabyBearExt4::ZERO; OUT]; geometry.num_chunks];

    worker.scope_with_threshold(num_blocks, (PAR_THRESHOLD / U).max(1), |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx) * U;
            let chunk_size = geometry.get_chunk_size(thread_idx) * U;
            let ext_inputs = ext_inputs.to_vec();
            let acc_dst = it.next().unwrap();

            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                let r11v = avx2::r11v();
                let const_bcast = avx2::soa_broadcast_ext(additive_constant);
                let has_const = !additive_constant.is_zero();

                let mut ext_flat = vec![0u32; ext_inputs.len() * U * ES];
                let mut form_flat = vec![0u32; forms.len() * U * ES];
                let mut lazy = vec![0u64; U * ES];
                let mut lazy_out = vec![0u32; ES];
                let mut acc_soa = vec![0u32; ES];
                let mut ext_tmp = vec![BabyBearExt4::ZERO; 8 * NG];
                let xptr = ext_flat.as_mut_ptr();
                let fptr = form_flat.as_mut_ptr();
                let lptr = lazy.as_mut_ptr();
                let tables_p: Vec<avx2::SoaExtTable> = products
                    .iter()
                    .map(|(_, _, c)| avx2::SoaExtTable::new(c))
                    .collect();
                let tables_q: Vec<avx2::SoaExtTable> = quads
                    .iter()
                    .map(|(_, _, c)| avx2::SoaExtTable::new(c))
                    .collect();
                let tables_l: Vec<avx2::SoaExtTable> = linear_terms
                    .iter()
                    .map(|(_, c)| avx2::SoaExtTable::new(c))
                    .collect();

                let mut block = chunk_start;
                while block < chunk_start + chunk_size {
                    for (i, src) in ext_inputs.iter().enumerate() {
                        let src_ptr = src.ptr as *const BabyBearExt4;
                        for u in 0..U {
                            fill_ext_w3_soa(
                                xptr.add((i * U + u) * ES),
                                src_ptr,
                                block + u,
                                interp[i],
                                ext_tmp.as_mut_ptr(),
                            );
                        }
                    }
                    for (f, form) in forms.iter().enumerate() {
                        for u in 0..U {
                            let g = fptr.add((f * U + u) * ES);
                            let mut it = form.members.iter();
                            match it.next() {
                                Some((op, idx)) => apply_ext_form_op_first(
                                    g,
                                    xptr.add((*idx as usize * U + u) * ES),
                                    op,
                                ),
                                None => core::ptr::write_bytes(g, 0, ES),
                            }
                            for (op, idx) in it {
                                apply_ext_form_op(g, xptr.add((*idx as usize * U + u) * ES), op);
                            }
                            if !form.constant.is_zero() {
                                avx2::soa_ext_form_add_base_const_n::<NBIN>(g, form.constant);
                            }
                        }
                    }
                    for ((a, b, _), tb) in products.iter().zip(tables_p.iter()) {
                        let pa = |u: usize| match a {
                            FormRef::Slot(i) => xptr.add((*i as usize * U + u) * ES),
                            FormRef::Form(i) => fptr.add((*i as usize * U + u) * ES),
                        };
                        let pb = |u: usize| match b {
                            FormRef::Slot(i) => xptr.add((*i as usize * U + u) * ES),
                            FormRef::Form(i) => fptr.add((*i as usize * U + u) * ES),
                        };
                        for u in 0..U {
                            avx2::soa_quad_ee_lazy::<NG>(lptr.add(u * ES), pa(u), pb(u), tb, r11v);
                        }
                    }
                    for ((a, b, _), tb) in quads.iter().zip(tables_q.iter()) {
                        for u in 0..U {
                            avx2::soa_quad_ee_lazy::<NG>(
                                lptr.add(u * ES),
                                xptr.add((*a as usize * U + u) * ES),
                                xptr.add((*b as usize * U + u) * ES),
                                tb,
                                r11v,
                            );
                        }
                    }
                    for ((i, _), tb) in linear_terms.iter().zip(tables_l.iter()) {
                        for u in 0..U {
                            avx2::soa_lin_ext_lazy::<NBIN>(
                                lptr.add(u * ES),
                                xptr.add((*i as usize * U + u) * ES),
                                tb,
                            );
                        }
                    }
                    for u in 0..U {
                        avx2::soa_lazy_finalize::<NG>(lptr.add(u * ES), lazy_out.as_mut_ptr());
                        if has_const {
                            avx2::soa_add_const_all_n::<NBIN>(lazy_out.as_mut_ptr(), &const_bcast);
                        }
                        let eqb = avx2::soa_broadcast_ext(&t_suffix[block + u]);
                        avx2::soa_apply_eq_and_accumulate_n::<NG>(
                            acc_soa.as_mut_ptr(),
                            lazy_out.as_mut_ptr(),
                            &eqb,
                            r11v,
                        );
                    }
                    block += U;
                }

                *acc_dst = finish_soa_acc(&acc_soa, &mut ext_tmp);
            })
        }
    });

    reduce_chunks(acc_chunks)
}

/// 8-tap Lagrange fold of a base column in LSB layout, 8 output rows per
/// call (requires `dst.len() % 8 == 0`).
pub(crate) fn lsb_fold_base_soa_parallel(
    src_ptr: *const u8,
    dst: &mut [BabyBearExt4],
    weights: &[BabyBearExt4; 8],
    worker: &Worker,
) {
    use crate::gkr::PAR_THRESHOLD;
    let rows = dst.len();
    assert_eq!(rows % 8, 0);
    let blocks = rows / 8;
    let dst_addr = dst.as_mut_ptr() as usize;
    let src_addr = src_ptr as usize;
    worker.scope_with_threshold(blocks, (PAR_THRESHOLD / 8).max(1), |scope, geometry| {
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                let prefix_limbs: [[core::arch::x86_64::__m256i; 4]; 8] =
                    core::array::from_fn(|i| avx2::soa_broadcast_ext(&weights[i]));
                let sp = src_addr as *const BabyBearField;
                let dp = dst_addr as *mut BabyBearExt4;
                for blk in chunk_start..(chunk_start + chunk_size) {
                    let limbs = avx2::lsb_soa_fold8_base(sp, &prefix_limbs, blk);
                    avx2::soa_store_ext8(&limbs, dp.add(8 * blk));
                }
            })
        }
    });
}

/// 8-tap Lagrange fold of an ext column in LSB layout, 8 output rows per
/// call (requires `dst.len() % 8 == 0`).
pub(crate) fn lsb_fold_ext_soa_parallel(
    src_ptr: *const u8,
    dst: &mut [BabyBearExt4],
    weights: &[BabyBearExt4; 8],
    worker: &Worker,
) {
    use crate::gkr::PAR_THRESHOLD;
    let rows = dst.len();
    assert_eq!(rows % 8, 0);
    let blocks = rows / 8;
    let dst_addr = dst.as_mut_ptr() as usize;
    let src_addr = src_ptr as usize;
    worker.scope_with_threshold(blocks, (PAR_THRESHOLD / 8).max(1), |scope, geometry| {
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| unsafe {
                let tables: [avx2::SoaExtTable; 8] =
                    core::array::from_fn(|i| avx2::SoaExtTable::new(&weights[i]));
                let sp = src_addr as *const BabyBearExt4;
                let dp = dst_addr as *mut BabyBearExt4;
                for blk in chunk_start..(chunk_start + chunk_size) {
                    let limbs = avx2::lsb_soa_fold8_ext(sp, &tables, blk);
                    avx2::soa_store_ext8(&limbs, dp.add(8 * blk));
                }
            })
        }
    });
}
