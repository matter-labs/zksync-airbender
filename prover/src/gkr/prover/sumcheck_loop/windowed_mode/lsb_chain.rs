//! Building blocks of the same-size LSB chains (uniskip and windowed): the
//! [`SameSizeChainOps`] trait over the per-pass kernels (reading either the
//! ORIGINAL layer inputs or the folded tables), the EXPLICIT non-merged
//! folds that materialize each pass's binding into the
//! [`FoldBufferTracker`] regions, and the scalar tail helpers. The
//! transcript (commit/draw), claim chaining, schedule walking, and all
//! self-checks live at the caller (`sumcheck_loop`'s case functions); this
//! module COMPUTES only.
//!
//! Platform dispatch: the chain executor is a [`GKRBackend`] ASSOCIATED
//! TYPE — [`GenericSameSizeChain`] here is the portable implementation over
//! the `lsb_generic` field-op kernels; arch-specialized executors (the NEON
//! one) live in their backend's arch-gated module. No `cfg(target_arch)`
//! appears in this module.
//!
//! Buffer discipline: every input poly gets one [`FoldBufferTracker`] over
//! its uninit scratch allocation (in `base_addrs ++ ext_addrs` slot order).
//! A pass reads plain borrowed slices (the originals, or the trackers'
//! input regions), its fold writes the trackers' OUTPUT regions, and the
//! caller then `step_to`s the trackers for the next stage — dense
//! contiguous regions throughout, exactly like the dimension-reducing
//! engine.
//!
//! [`GKRBackend`]: crate::gkr::prover::gkr_backend::GKRBackend

use super::lsb_generic;
use crate::gkr::prover::dimension_reduction::lsb_backward::FoldBufferTracker;
use crate::gkr::sumcheck::access_and_fold::DisjointAccessQuasiSlice;
use crate::worker::Worker;
use field::{Field, FieldExtension, PrimeField};

/// The per-layer same-size chain executor: owns the compiled SoA program
/// and whatever kernel tables the platform needs. Constructed per layer by
/// the backend
/// ([`GKRBackend::make_same_size_chain`](crate::gkr::prover::gkr_backend::GKRBackend::make_same_size_chain));
/// every method is a pure computation — the polys come in as plain borrowed
/// slices (`*_initial_*` reads the original layer inputs in
/// `base ++ ext` slot order, `*_continuing_*` the folded tables from the
/// trackers' input regions).
pub trait SameSizeChainOps<F: PrimeField, E: FieldExtension<F> + Field> {
    /// INITIAL width-3 uniskip pass: the 16-point univariate of the packed
    /// q over the original inputs. `eq_suffix` covers the variables ABOVE
    /// the pass's window; `out_size` is its length (remaining rows).
    fn uniskip_initial_pass(
        &self,
        base_polys: &[&[F]],
        ext_polys: &[&[E]],
        eq_suffix: &[E],
        out_size: usize,
        worker: &Worker,
    ) -> [E; 16];

    /// CONTINUING width-3 uniskip pass over the folded tables.
    fn uniskip_continuing_pass(
        &self,
        folded: &[&[E]],
        eq_suffix: &[E],
        out_size: usize,
        worker: &Worker,
    ) -> [E; 16];

    /// INITIAL width-3 window pass: the T-weighted `{0,1,inf}^3` accumulator
    /// over the original inputs.
    fn window_initial_pass(
        &self,
        base_polys: &[&[F]],
        ext_polys: &[&[E]],
        eq_suffix: &[E],
        out_size: usize,
        worker: &Worker,
    ) -> [E; 27];

    /// CONTINUING width-3 window pass over the folded tables.
    fn window_continuing_pass(
        &self,
        folded: &[&[E]],
        eq_suffix: &[E],
        out_size: usize,
        worker: &Worker,
    ) -> [E; 27];

    /// The EXPLICIT fold after the INITIAL pass: every original poly is
    /// folded by the 8 window weights into its tracker's OUTPUT region.
    fn fold_initial(
        &self,
        base_polys: &[&[F]],
        ext_polys: &[&[E]],
        weights: &[E; 8],
        trackers: &mut [FoldBufferTracker<E>],
        worker: &Worker,
    );

    /// The EXPLICIT fold after a CONTINUING pass: every tracker's INPUT
    /// region is folded by the 8 window weights into its OUTPUT region.
    fn fold_continuing(
        &self,
        weights: &[E; 8],
        trackers: &mut [FoldBufferTracker<E>],
        worker: &Worker,
    );

    /// One scalar tail round's message pair `(h(0), leading coefficient)`
    /// over the trackers' input regions, weighted by the contracted suffix
    /// eq table.
    fn tail_round_message(
        &self,
        trackers: &[FoldBufferTracker<E>],
        tail_t_table: &[E],
        worker: &Worker,
    ) -> (E, E);
}

/// The portable chain executor over the `lsb_generic` field-op kernels:
/// works for every `<F, E>` pair on every architecture.
pub struct GenericSameSizeChain<F: PrimeField, E: FieldExtension<F> + Field> {
    prog: super::program::OwnedSoaProgram<F, E>,
    mat: lsb_generic::Lde8Matrix<F>,
}

impl<F: PrimeField + field::TwoAdicField, E: FieldExtension<F> + Field> GenericSameSizeChain<F, E> {
    pub fn new(prog: super::program::OwnedSoaProgram<F, E>) -> Self {
        let omega16_f: F = ::fft::domain_generator_for_size::<F>(16);
        Self {
            prog,
            mat: lsb_generic::Lde8Matrix::new(omega16_f),
        }
    }
}

/// Wraps plain borrowed slices into the kernels' access type (a raw
/// pointer + length view; no interior mutability is exercised).
pub fn quasi<T: Send + Sync, const A: bool>(
    slices: &[&[T]],
) -> Vec<DisjointAccessQuasiSlice<T, A>> {
    slices
        .iter()
        .map(|s| DisjointAccessQuasiSlice::<_, A>::from_init_slice(s))
        .collect()
}

impl<F: PrimeField, E: FieldExtension<F> + Field> SameSizeChainOps<F, E>
    for GenericSameSizeChain<F, E>
where
    [(); E::DEGREE]: Sized,
{
    fn uniskip_initial_pass(
        &self,
        base_polys: &[&[F]],
        ext_polys: &[&[E]],
        eq_suffix: &[E],
        out_size: usize,
        worker: &Worker,
    ) -> [E; 16] {
        lsb_generic::head_pass::<F, E>(
            &quasi::<F, false>(base_polys),
            &quasi::<E, false>(ext_polys),
            &self.prog,
            &self.mat,
            eq_suffix,
            out_size,
            worker,
        )
    }

    fn uniskip_continuing_pass(
        &self,
        folded: &[&[E]],
        eq_suffix: &[E],
        out_size: usize,
        worker: &Worker,
    ) -> [E; 16] {
        lsb_generic::ext_pass::<F, E>(
            &quasi::<E, false>(folded),
            &self.prog,
            &self.mat,
            eq_suffix,
            out_size,
            worker,
        )
    }

    fn window_initial_pass(
        &self,
        base_polys: &[&[F]],
        ext_polys: &[&[E]],
        eq_suffix: &[E],
        out_size: usize,
        worker: &Worker,
    ) -> [E; 27] {
        lsb_generic::window27_head_pass::<F, E>(
            &quasi::<F, false>(base_polys),
            &quasi::<E, false>(ext_polys),
            &self.prog,
            eq_suffix,
            out_size,
            worker,
        )
    }

    fn window_continuing_pass(
        &self,
        folded: &[&[E]],
        eq_suffix: &[E],
        out_size: usize,
        worker: &Worker,
    ) -> [E; 27] {
        lsb_generic::window27_ext_pass::<F, E>(
            &quasi::<E, false>(folded),
            &self.prog,
            eq_suffix,
            out_size,
            worker,
        )
    }

    fn fold_initial(
        &self,
        base_polys: &[&[F]],
        ext_polys: &[&[E]],
        weights: &[E; 8],
        trackers: &mut [FoldBufferTracker<E>],
        worker: &Worker,
    ) {
        let nb = base_polys.len();
        assert_eq!(trackers.len(), nb + ext_polys.len());
        for (i, src) in base_polys.iter().enumerate() {
            let dst = chain_fold_dst(&trackers[i], src.len() / 8);
            let src = DisjointAccessQuasiSlice::<_, false>::from_init_slice(src);
            lsb_generic::fold_base::<F, E>(&src, dst, weights, worker);
        }
        for (i, src) in ext_polys.iter().enumerate() {
            let dst = chain_fold_dst(&trackers[nb + i], src.len() / 8);
            lsb_generic::fold_ext::<E>(
                crate::gkr::prover::SendConstPtr(src.as_ptr()),
                dst,
                weights,
                worker,
            );
        }
    }

    fn fold_continuing(
        &self,
        weights: &[E; 8],
        trackers: &mut [FoldBufferTracker<E>],
        worker: &Worker,
    ) {
        for tracker in trackers.iter_mut() {
            let fold_out = tracker.output_len();
            assert_eq!(tracker.input_len(), 8 * fold_out);
            let src_ptr = tracker.input_ptr_range().start;
            let dst = chain_fold_dst(tracker, fold_out);
            lsb_generic::fold_ext::<E>(
                crate::gkr::prover::SendConstPtr(src_ptr),
                dst,
                weights,
                worker,
            );
        }
    }

    fn tail_round_message(
        &self,
        trackers: &[FoldBufferTracker<E>],
        tail_t_table: &[E],
        worker: &Worker,
    ) -> (E, E) {
        tail_round_message_with_program(&self.prog, trackers, tail_t_table, worker)
    }
}

/// The tracker's output region as a mutable slice for a fold of
/// `expected_len` values (asserted against the tracker's own sizing).
///
/// The mutable-alias discipline is the tracker's contract: the output
/// region is disjoint from the input region and exclusively owned by the
/// fold that writes it.
pub fn chain_fold_dst<E>(tracker: &FoldBufferTracker<E>, expected_len: usize) -> &'static mut [E] {
    assert_eq!(tracker.output_len(), expected_len);
    unsafe { core::slice::from_raw_parts_mut(tracker.output_ptr_range().start, expected_len) }
}

/// One scalar tail round's message pair `(h(0), leading coefficient)`: the
/// folded program evaluated over the adjacent pairs of every tracker's
/// INPUT region, weighted by the contracted suffix eq table. Parallel over
/// pairs; small tails collapse to a single chunk under the worker
/// threshold. Shared by every executor (the tail is scalar work).
pub fn tail_round_message_with_program<F: PrimeField, E: FieldExtension<F> + Field>(
    prog: &super::program::OwnedSoaProgram<F, E>,
    trackers: &[FoldBufferTracker<E>],
    tail_t_table: &[E],
    worker: &Worker,
) -> (E, E) {
    use crate::gkr::prover::SendConstPtr;
    use crate::gkr::PAR_THRESHOLD;

    let pairs = trackers[0].input_len() / 2;
    assert_eq!(tail_t_table.len(), pairs);
    let slot_ptrs: Vec<SendConstPtr<E>> = trackers
        .iter()
        .map(|t| {
            assert_eq!(t.input_len(), 2 * pairs);
            SendConstPtr(t.input_ptr_range().start)
        })
        .collect();
    let num_slots = slot_ptrs.len();

    let geometry = worker.get_geometry_with_threshold(pairs, PAR_THRESHOLD);
    let mut partials: Vec<(E, E)> = vec![(E::ZERO, E::ZERO); geometry.num_chunks];
    worker.scope_with_threshold(pairs, PAR_THRESHOLD, |scope, geometry| {
        let mut it = partials.iter_mut();
        let slot_ptrs = &slot_ptrs;
        for thread_idx in 0..geometry.num_chunks {
            let chunk_start = geometry.get_chunk_start_pos(thread_idx);
            let chunk_size = geometry.get_chunk_size(thread_idx);
            let dst = it.next().unwrap();
            Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                let mut v0s: Vec<E> = vec![E::ZERO; num_slots];
                let mut dts: Vec<E> = vec![E::ZERO; num_slots];
                let mut form0: Vec<E> = vec![E::ZERO; prog.forms.len()];
                let mut formd: Vec<E> = vec![E::ZERO; prog.forms.len()];
                let (h0, hinf) = dst;
                for j in chunk_start..(chunk_start + chunk_size) {
                    let (g0, ginf) = tail_eval_pair::<F, E>(
                        prog, slot_ptrs, j, &mut v0s, &mut dts, &mut form0, &mut formd,
                    );
                    let w = tail_t_table[j];
                    let mut t0 = g0;
                    t0.mul_assign(&w);
                    h0.add_assign(&t0);
                    let mut ti = ginf;
                    ti.mul_assign(&w);
                    hinf.add_assign(&ti);
                }
            })
        }
    });

    let mut h0 = E::ZERO;
    let mut hinf = E::ZERO;
    for (p0, pinf) in partials.into_iter() {
        h0.add_assign(&p0);
        hinf.add_assign(&pinf);
    }
    (h0, hinf)
}

/// The folded program's `(G(0), leading coefficient)` on ONE adjacent input
/// pair: linear forms at X = 0 and on the differences, then products and
/// expanded quadratic terms (the affine parts vanish at infinity).
#[inline(always)]
#[allow(clippy::too_many_arguments)]
fn tail_eval_pair<F: PrimeField, E: FieldExtension<F> + Field>(
    prog: &super::program::OwnedSoaProgram<F, E>,
    slot_ptrs: &[crate::gkr::prover::SendConstPtr<E>],
    j: usize,
    v0s: &mut [E],
    dts: &mut [E],
    form0: &mut [E],
    formd: &mut [E],
) -> (E, E) {
    for (slot, ptr) in slot_ptrs.iter().enumerate() {
        let v0 = unsafe { *ptr.get().add(2 * j) };
        let v1 = unsafe { *ptr.get().add(2 * j + 1) };
        let mut d = v1;
        d.sub_assign(&v0);
        v0s[slot] = v0;
        dts[slot] = d;
    }
    for (fi, members) in prog.forms.iter().enumerate() {
        let mut a0 = E::ZERO;
        let mut ad = E::ZERO;
        for (op, idx) in members.iter() {
            let (x0, xd) = (v0s[*idx as usize], dts[*idx as usize]);
            match op {
                super::program::FormOp::Add => {
                    a0.add_assign(&x0);
                    ad.add_assign(&xd);
                }
                super::program::FormOp::Sub => {
                    a0.sub_assign(&x0);
                    ad.sub_assign(&xd);
                }
                super::program::FormOp::Mul(c) => {
                    let mut t0 = x0;
                    t0.mul_assign_by_base(c);
                    a0.add_assign(&t0);
                    let mut td = xd;
                    td.mul_assign_by_base(c);
                    ad.add_assign(&td);
                }
            }
        }
        form0[fi] = a0;
        formd[fi] = ad;
    }
    let mut g0 = prog.additive_constant;
    let mut ginf = E::ZERO;
    for (a, f, c) in prog.products.iter() {
        let mut t0 = v0s[*a as usize];
        t0.mul_assign(&form0[*f as usize]);
        t0.mul_assign(c);
        g0.add_assign(&t0);
        let mut ti = dts[*a as usize];
        ti.mul_assign(&formd[*f as usize]);
        ti.mul_assign(c);
        ginf.add_assign(&ti);
    }
    for (a, b, c) in prog.folded_quad.iter() {
        let mut t0 = v0s[*a as usize];
        t0.mul_assign(&v0s[*b as usize]);
        t0.mul_assign(c);
        g0.add_assign(&t0);
        let mut ti = dts[*a as usize];
        ti.mul_assign(&dts[*b as usize]);
        ti.mul_assign(c);
        ginf.add_assign(&ti);
    }
    for (i, c) in prog.folded_lin.iter() {
        let mut t0 = v0s[*i as usize];
        t0.mul_assign(c);
        g0.add_assign(&t0);
    }
    (g0, ginf)
}

/// Folds every tracker's INPUT region by `(1 - r, r)` over adjacent pairs
/// into its OUTPUT region. Parallel over pairs; the regions are disjoint by
/// the tracker's construction. Executor-independent (plain scalar folds).
pub fn tail_fold_trackers<E: Field>(trackers: &mut [FoldBufferTracker<E>], r: &E, worker: &Worker) {
    use crate::gkr::prover::{SendConstPtr, SendPtr};
    use crate::gkr::PAR_THRESHOLD;

    for tracker in trackers.iter_mut() {
        let pairs = tracker.input_len() / 2;
        assert_eq!(tracker.output_len(), pairs);
        let src = SendConstPtr(tracker.input_ptr_range().start);
        let dst = SendPtr(tracker.output_ptr_range().start);
        worker.scope_with_threshold(pairs, PAR_THRESHOLD, |scope, geometry| {
            for thread_idx in 0..geometry.num_chunks {
                let chunk_start = geometry.get_chunk_start_pos(thread_idx);
                let chunk_size = geometry.get_chunk_size(thread_idx);
                Worker::smart_spawn(scope, thread_idx == geometry.len() - 1, move |_| {
                    let sp = src.get();
                    let dp = dst.get();
                    for j in chunk_start..(chunk_start + chunk_size) {
                        let v0 = unsafe { *sp.add(2 * j) };
                        let v1 = unsafe { *sp.add(2 * j + 1) };
                        let mut v = v1;
                        v.sub_assign(&v0);
                        v.mul_assign(r);
                        v.add_assign(&v0);
                        unsafe {
                            dp.add(j).write(v);
                        }
                    }
                })
            }
        });
    }
}
