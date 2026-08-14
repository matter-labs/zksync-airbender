//! Portable (arch-independent) kernels for the LSB uniskip chain: the same
//! pass/fold semantics as the NEON `lsb_bench` set, in plain field ops. Used
//! on non-aarch64 targets and for non-BabyBear field pairs; the chain driver
//! (`lsb_chain`) picks NEON or these per platform, so proofs are identical
//! either way.
//!
//! Domain layout (see `windowed_mode::uniskip`): a pass's 16-point grid is
//! [8 raw values at H = <w8> in node order, 8 interpolated values at the odd
//! points w16^(2i+1)]; the coset half is one 8x8 base-field Lagrange matrix
//! per slot.

use crate::gkr::prover::sumcheck_loop::windowed_mode::bench::{
    BenchStep, FormOp, OwnedSoaProgram,
};
use crate::gkr::prover::{SendConstPtr, SendPtr};
use crate::gkr::sumcheck::access_and_fold::DisjointAccessQuasiSlice;
use crate::gkr::PAR_THRESHOLD;
use crate::worker::Worker;
use field::{Field, FieldExtension, PrimeField};

/// The 8x8 base-field matrix taking a slot's 8 raw values (on H, node order)
/// to its 8 values on the odd half of <w16>: m[i][j] = L_j(w16^(2i+1)).
#[derive(Clone, Copy)]
pub(crate) struct Lde8Matrix<F: PrimeField> {
    pub m: [[F; 8]; 8],
}

impl<F: PrimeField> Lde8Matrix<F> {
    pub(crate) fn new(omega16: F) -> Self {
        let mut omega8 = omega16;
        omega8.square();
        let nodes: [F; 8] = core::array::from_fn(|k| omega8.pow(k as u32));
        let d_consts: [F; 8] = core::array::from_fn(|j| {
            let mut d = F::ONE;
            for k in 0..8 {
                if k != j {
                    let mut t = nodes[j];
                    t.sub_assign(&nodes[k]);
                    d.mul_assign(&t);
                }
            }
            d.inverse().expect("distinct interpolation nodes")
        });
        let m = core::array::from_fn(|i| {
            let x = omega16.pow((2 * i + 1) as u32);
            core::array::from_fn(|j| {
                let mut l = d_consts[j];
                for k in 0..8 {
                    if k != j {
                        let mut t = x;
                        t.sub_assign(&nodes[k]);
                        l.mul_assign(&t);
                    }
                }
                l
            })
        });
        Self { m }
    }
}

#[inline(always)]
fn extend_base_grid<F: PrimeField>(grid: &mut [F; 16], lde: &Lde8Matrix<F>) {
    for i in 0..8 {
        let mut acc = F::ZERO;
        for k in 0..8 {
            let mut t = lde.m[i][k];
            t.mul_assign(&grid[k]);
            acc.add_assign(&t);
        }
        grid[8 + i] = acc;
    }
}

#[inline(always)]
fn extend_ext_grid<F: PrimeField, E: FieldExtension<F> + Field>(
    grid: &mut [E; 16],
    lde: &Lde8Matrix<F>,
) {
    for i in 0..8 {
        let mut acc = E::ZERO;
        for k in 0..8 {
            let mut t = grid[k];
            t.mul_assign_by_base(&lde.m[i][k]);
            acc.add_assign(&t);
        }
        grid[8 + i] = acc;
    }
}

/// Head pass (pass 0): sources are the layer's original base/ext polynomials
/// read in natural order, 8 consecutive values per suffix index. Returns the
/// eq-weighted 16 domain evaluations of q_0.
#[allow(clippy::too_many_arguments)]
pub(crate) fn head_pass<F: PrimeField, E: FieldExtension<F> + Field>(
    base_sources: &[DisjointAccessQuasiSlice<F, false>],
    ext_sources: &[DisjointAccessQuasiSlice<E, false>],
    prog: &OwnedSoaProgram<F, E>,
    lde: &Lde8Matrix<F>,
    eq_suffix: &[E],
    out_size: usize,
    worker: &Worker,
) -> [E; 16] {
    assert_eq!(eq_suffix.len(), out_size.max(1));
    let geometry = worker.get_geometry_with_threshold(out_size, PAR_THRESHOLD);
    let mut acc_chunks: Vec<([E; 16], E)> = vec![([E::ZERO; 16], E::ZERO); geometry.num_chunks];

    worker.scope_with_threshold(out_size, PAR_THRESHOLD, |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let base_sources = base_sources.to_vec();
            let ext_sources = ext_sources.to_vec();
            let acc_dst = it.next().unwrap();
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let mut bgrids: Vec<[F; 16]> = vec![[F::ZERO; 16]; base_sources.len()];
                let mut egrids: Vec<[E; 16]> = vec![[E::ZERO; 16]; ext_sources.len()];
                let mut fvals: Vec<[F; 16]> = vec![[F::ZERO; 16]; prog.forms.len()];
                let (q16, eq_sum) = acc_dst;
                for j in chunk_start..(chunk_start + chunk_size) {
                    for (s, src) in base_sources.iter().enumerate() {
                        for i in 0..8 {
                            bgrids[s][i] = src.read(8 * j + i);
                        }
                        extend_base_grid(&mut bgrids[s], lde);
                    }
                    for (s, src) in ext_sources.iter().enumerate() {
                        for i in 0..8 {
                            egrids[s][i] = src.read(8 * j + i);
                        }
                        extend_ext_grid(&mut egrids[s], lde);
                    }
                    apply_base_forms(&prog.forms, &bgrids, &mut fvals);
                    for p in 0..16 {
                        let mut g = E::ZERO;
                        for (a, f, c) in prog.products.iter() {
                            let mut t = bgrids[*a as usize][p];
                            t.mul_assign(&fvals[*f as usize][p]);
                            let mut tc = *c;
                            tc.mul_assign_by_base(&t);
                            g.add_assign(&tc);
                        }
                        for step in prog.rest_steps.iter() {
                            match step {
                                BenchStep::QuadBB { a, b, c } => {
                                    let mut t = bgrids[*a as usize][p];
                                    t.mul_assign(&bgrids[*b as usize][p]);
                                    let mut tc = *c;
                                    tc.mul_assign_by_base(&t);
                                    g.add_assign(&tc);
                                }
                                BenchStep::QuadBE { base, ext, c } => {
                                    let mut t = egrids[*ext as usize][p];
                                    t.mul_assign_by_base(&bgrids[*base as usize][p]);
                                    t.mul_assign(c);
                                    g.add_assign(&t);
                                }
                                BenchStep::QuadEE { a, b, c } => {
                                    let mut t = egrids[*a as usize][p];
                                    t.mul_assign(&egrids[*b as usize][p]);
                                    t.mul_assign(c);
                                    g.add_assign(&t);
                                }
                                BenchStep::LinB { i, c } => {
                                    let mut tc = *c;
                                    tc.mul_assign_by_base(&bgrids[*i as usize][p]);
                                    g.add_assign(&tc);
                                }
                                BenchStep::LinE { i, c } => {
                                    let mut t = egrids[*i as usize][p];
                                    t.mul_assign(c);
                                    g.add_assign(&t);
                                }
                            }
                        }
                        g.mul_assign(&eq_suffix[j]);
                        q16[p].add_assign(&g);
                    }
                    eq_sum.add_assign(&eq_suffix[j]);
                }
            })
        }
    });

    reduce_with_constant(acc_chunks, &prog.additive_constant)
}

/// Ext pass (pass > 0): all sources are already-folded extension-field
/// tables over the COMBINED slot space (base-then-ext order); the program is
/// the folded one (forms + products + folded_quad + folded_lin + constant).
#[allow(clippy::too_many_arguments)]
pub(crate) fn ext_pass<F: PrimeField, E: FieldExtension<F> + Field>(
    srcs: &[DisjointAccessQuasiSlice<E, false>],
    prog: &OwnedSoaProgram<F, E>,
    lde: &Lde8Matrix<F>,
    eq_suffix: &[E],
    out_size: usize,
    worker: &Worker,
) -> [E; 16] {
    assert_eq!(eq_suffix.len(), out_size.max(1));
    let geometry = worker.get_geometry_with_threshold(out_size, PAR_THRESHOLD);
    let mut acc_chunks: Vec<([E; 16], E)> = vec![([E::ZERO; 16], E::ZERO); geometry.num_chunks];

    worker.scope_with_threshold(out_size, PAR_THRESHOLD, |scope, geometry| {
        let mut it = acc_chunks.iter_mut();
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let srcs = srcs.to_vec();
            let acc_dst = it.next().unwrap();
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let mut grids: Vec<[E; 16]> = vec![[E::ZERO; 16]; srcs.len()];
                let mut fvals: Vec<[E; 16]> = vec![[E::ZERO; 16]; prog.forms.len()];
                let (q16, eq_sum) = acc_dst;
                for j in chunk_start..(chunk_start + chunk_size) {
                    for (s, src) in srcs.iter().enumerate() {
                        for i in 0..8 {
                            grids[s][i] = src.read(8 * j + i);
                        }
                        extend_ext_grid(&mut grids[s], lde);
                    }
                    apply_ext_forms(&prog.forms, &grids, &mut fvals);
                    for p in 0..16 {
                        let mut g = E::ZERO;
                        for (a, f, c) in prog.products.iter() {
                            let mut t = grids[*a as usize][p];
                            t.mul_assign(&fvals[*f as usize][p]);
                            t.mul_assign(c);
                            g.add_assign(&t);
                        }
                        for (a, b, c) in prog.folded_quad.iter() {
                            let mut t = grids[*a as usize][p];
                            t.mul_assign(&grids[*b as usize][p]);
                            t.mul_assign(c);
                            g.add_assign(&t);
                        }
                        for (i, c) in prog.folded_lin.iter() {
                            let mut t = grids[*i as usize][p];
                            t.mul_assign(c);
                            g.add_assign(&t);
                        }
                        g.mul_assign(&eq_suffix[j]);
                        q16[p].add_assign(&g);
                    }
                    eq_sum.add_assign(&eq_suffix[j]);
                }
            })
        }
    });

    reduce_with_constant(acc_chunks, &prog.additive_constant)
}

#[inline(always)]
fn apply_base_forms<F: PrimeField>(
    forms: &[Vec<(FormOp<F>, u16)>],
    grids: &[[F; 16]],
    fvals: &mut [[F; 16]],
) {
    for (fi, members) in forms.iter().enumerate() {
        fvals[fi] = [F::ZERO; 16];
        for (op, idx) in members.iter() {
            let src = &grids[*idx as usize];
            for p in 0..16 {
                match op {
                    FormOp::Add => {
                        fvals[fi][p].add_assign(&src[p]);
                    }
                    FormOp::Sub => {
                        fvals[fi][p].sub_assign(&src[p]);
                    }
                    FormOp::Mul(c) => {
                        let mut t = src[p];
                        t.mul_assign(c);
                        fvals[fi][p].add_assign(&t);
                    }
                }
            }
        }
    }
}

#[inline(always)]
fn apply_ext_forms<F: PrimeField, E: FieldExtension<F> + Field>(
    forms: &[Vec<(FormOp<F>, u16)>],
    grids: &[[E; 16]],
    fvals: &mut [[E; 16]],
) {
    for (fi, members) in forms.iter().enumerate() {
        fvals[fi] = [E::ZERO; 16];
        for (op, idx) in members.iter() {
            let src = &grids[*idx as usize];
            for p in 0..16 {
                match op {
                    FormOp::Add => {
                        fvals[fi][p].add_assign(&src[p]);
                    }
                    FormOp::Sub => {
                        fvals[fi][p].sub_assign(&src[p]);
                    }
                    FormOp::Mul(c) => {
                        let mut t = src[p];
                        t.mul_assign_by_base(c);
                        fvals[fi][p].add_assign(&t);
                    }
                }
            }
        }
    }
}

/// Chunk reduce + the constant term: G's additive constant contributes
/// `constant * sum_j eq[j]` to EVERY domain point.
fn reduce_with_constant<E: Field>(acc_chunks: Vec<([E; 16], E)>, constant: &E) -> [E; 16] {
    let mut q16 = [E::ZERO; 16];
    let mut eq_sum = E::ZERO;
    for (part, eq_part) in acc_chunks.into_iter() {
        for p in 0..16 {
            q16[p].add_assign(&part[p]);
        }
        eq_sum.add_assign(&eq_part);
    }
    let mut c = *constant;
    c.mul_assign(&eq_sum);
    for p in 0..16 {
        q16[p].add_assign(&c);
    }
    q16
}

/// Fold a base-field source 8 -> 1 with the challenge's Lagrange weights:
/// `dst[j] = sum_i weights[i] * src[8j + i]`.
pub(crate) fn fold_base<F: PrimeField, E: FieldExtension<F> + Field>(
    src: &DisjointAccessQuasiSlice<F, false>,
    dst: &mut [E],
    weights: &[E; 8],
    worker: &Worker,
) {
    let rows = dst.len();
    let dst_ptr = SendPtr(dst.as_mut_ptr());
    let src = src.clone();
    worker.scope_with_threshold(rows, PAR_THRESHOLD, |scope, geometry| {
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let src = src.clone();
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let dp = dst_ptr.get();
                for row in chunk_start..(chunk_start + chunk_size) {
                    let mut acc = E::ZERO;
                    for i in 0..8 {
                        let mut t = weights[i];
                        t.mul_assign_by_base(&src.read(8 * row + i));
                        acc.add_assign(&t);
                    }
                    unsafe { dp.add(row).write(acc) };
                }
            })
        }
    });
}

/// Fold an extension-field table 8 -> 1 with the challenge's Lagrange
/// weights. `src` may alias `dst`'s allocation (disjoint live/next arena
/// regions), hence the raw-pointer carrier.
pub(crate) fn fold_ext<E: Field>(
    src: SendConstPtr<E>,
    dst: &mut [E],
    weights: &[E; 8],
    worker: &Worker,
) {
    let rows = dst.len();
    let dst_ptr = SendPtr(dst.as_mut_ptr());
    worker.scope_with_threshold(rows, PAR_THRESHOLD, |scope, geometry| {
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let sp = src.get();
                let dp = dst_ptr.get();
                for row in chunk_start..(chunk_start + chunk_size) {
                    let mut acc = E::ZERO;
                    for i in 0..8 {
                        let mut t = weights[i];
                        t.mul_assign(unsafe { &*sp.add(8 * row + i) });
                        acc.add_assign(&t);
                    }
                    unsafe { dp.add(row).write(acc) };
                }
            })
        }
    });
}
