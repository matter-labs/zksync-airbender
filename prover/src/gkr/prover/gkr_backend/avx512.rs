//! The x86-64 BabyBear/Ext4 backend with RUNTIME feature dispatch: the same
//! backend surface as [`Avx2GKRBackend`](super::avx2::Avx2GKRBackend), with
//! the same-size chain executor running the 16-lane `lsb_avx512` window
//! passes and folds and the dimension-reducing rounds running the
//! `avx512_dr` SoA chunk kernels when `avx512f` is available (the AVX2
//! executor and kernels otherwise), plus a pre-touched FOLD BUFFER POOL
//! shared by the dimension-reducing scratch and every same-size layer and
//! the cross-proof pool of the storage's extension polys. The
//! dimension-reduction forward ops are AVX-512 SoA above a size cutover and
//! serial below it.
//! Every value it produces is byte-identical to the naive and AVX2 backends'.
//!
//! [`X86GKRBackend::default()`] detects `avx512f` and enables the pool; it is
//! the [`DefaultBabyBearGKRBackend`](super::DefaultBabyBearGKRBackend) on
//! AVX2-enabled x86-64 builds. `X86GKRBackend::new(use_avx512, pooled)`
//! selects explicitly (for A/B runs).

use std::collections::BTreeMap;
use std::sync::Mutex;

use super::super::dimension_reduction::forward::DimensionReducingInputOutput;
use super::super::dimension_reduction::lsb_backward::FoldBufferTracker;
use super::super::{GKRAddress, GKRStorage, SumcheckIntermediateProofValues};
use super::avx2::{avx2_continuing_chunk, avx2_initial_chunk};
use super::{DimReducingSumcheckScratch, GKRBackend};
use crate::gkr::prover::sumcheck_loop::windowed_mode::{lsb_avx2, lsb_avx512, lsb_generic};
use crate::gkr::prover::EvaluationPointEntry;
use ::field::baby_bear::{base::BabyBearField, ext4::BabyBearExt4};
use cs::gkr_compiler::{GKRCircuitArtifact, OutputType};
use field::Field;
use transcript::Transcript;
use worker::Worker;

pub type FoldBuf = Box<[core::mem::MaybeUninit<BabyBearExt4>]>;

/// Pre-touched pool of uninit fold buffers, handed out by capacity (the
/// smallest sufficient buffers first) and returned after each layer. Sized
/// once per proving run from the circuit's shapes by
/// [`GKRBackend::prepare_fold_pool`]; misses fall back to fresh
/// allocations (and are reported).
pub struct FoldBufferPool {
    free: Mutex<Vec<FoldBuf>>,
    enabled: bool,
}

impl FoldBufferPool {
    fn new(enabled: bool) -> Self {
        Self {
            free: Mutex::new(Vec::new()),
            enabled,
        }
    }

    /// Allocate + first-touch the buffers of every `(count, capacity)` shape
    /// (touching in parallel over the worker so the page faults are paid
    /// here, once, instead of inside the first fold of every layer).
    fn prefill(&self, shapes: &[(usize, usize)], worker: &Worker) {
        if !self.enabled {
            return;
        }
        let t = std::time::Instant::now();
        // top up: buffers already in the pool (from a previous proof) cover
        // the shapes largest-first, only the shortfall is allocated + touched
        let mut have: Vec<FoldBuf> = core::mem::take(&mut *self.free.lock().unwrap());
        have.sort_by_key(|b| core::cmp::Reverse(b.len()));
        let mut ordered: Vec<(usize, usize)> = shapes.to_vec();
        ordered.sort_by_key(|&(_, cap)| core::cmp::Reverse(cap));
        let mut bufs: Vec<FoldBuf> = Vec::new();
        let mut kept: Vec<FoldBuf> = Vec::new();
        for &(count, cap) in ordered.iter() {
            let mut covered = 0usize;
            while covered < count {
                match have.iter().position(|b| b.len() >= cap) {
                    Some(pos) => {
                        // largest-first: the first sufficient one is the largest left
                        kept.push(have.remove(pos));
                        covered += 1;
                    }
                    None => break,
                }
            }
            for _ in covered..count {
                bufs.push(Box::new_uninit_slice(cap));
            }
        }
        let total: usize = bufs.iter().map(|b| b.len()).sum();
        let fresh = bufs.len();
        let addrs: Vec<(usize, usize)> = bufs
            .iter_mut()
            .map(|b| (b.as_mut_ptr() as usize, b.len() * core::mem::size_of::<BabyBearExt4>()))
            .collect();
        // touch: one write per 4 KB page of every buffer, pages split over the worker
        let pages: Vec<(usize, usize)> = addrs
            .iter()
            .flat_map(|&(a, bytes)| (0..bytes).step_by(4096).map(move |o| (a, o)))
            .collect();
        if !pages.is_empty() {
            worker.scope(pages.len(), |scope, geometry| {
                for idx in 0..geometry.len() {
                    let start = geometry.get_chunk_start_pos(idx);
                    let size = geometry.get_chunk_size(idx);
                    let pages = &pages;
                    Worker::smart_spawn(scope, idx == geometry.len() - 1, move |_| {
                        for &(a, o) in &pages[start..start + size] {
                            unsafe { core::ptr::write_volatile((a as *mut u8).add(o), 0u8) };
                        }
                    });
                }
            });
        }
        let mut free = self.free.lock().unwrap();
        // everything back: the reused ones, the previously unmatched ones, the fresh ones
        free.extend(kept);
        free.extend(have);
        free.extend(bufs);
        free.sort_by_key(|b| b.len());
        println!(
            "[pool] fold buffers: {} in pool, {fresh} fresh ({:.1} MB) for shapes {:?}, in {:?}",
            free.len(),
            (total * core::mem::size_of::<BabyBearExt4>()) as f64 / 1e6,
            shapes,
            t.elapsed()
        );
    }

    /// `count` buffers of at least `cap` elements: the smallest sufficient
    /// pooled ones, fresh allocations for the rest.
    fn take(&self, count: usize, cap: usize) -> Vec<FoldBuf> {
        let mut out = Vec::with_capacity(count);
        if self.enabled {
            let mut free = self.free.lock().unwrap();
            // sorted ascending by len: the first sufficient index and onwards
            while out.len() < count {
                let Some(pos) = free.iter().position(|b| b.len() >= cap) else {
                    break;
                };
                out.push(free.remove(pos));
            }
        }
        if out.len() < count {
            if self.enabled {
                println!(
                    "[pool] miss: {} of {} buffers of {} elements allocated fresh",
                    count - out.len(),
                    count,
                    cap
                );
            }
            while out.len() < count {
                out.push(Box::new_uninit_slice(cap));
            }
        }
        out
    }

    fn give(&self, bufs: Vec<FoldBuf>) {
        if !self.enabled {
            return;
        }
        let mut free = self.free.lock().unwrap();
        free.extend(bufs);
        free.sort_by_key(|b| b.len());
    }
}

/// The x86-64 AVX-512 + BabyBear/Ext4 same-size chain executor: window
/// passes and folds through the `lsb_avx512` kernels, the (unreachable)
/// uniskip schedule and odd shapes through the AVX2 / portable kernels.
pub struct Avx512SameSizeChain {
    prog: crate::gkr::prover::sumcheck_loop::OwnedSoaProgram<BabyBearField, BabyBearExt4>,
    folded_interp: Vec<bool>,
    mat: lsb_generic::Lde8Matrix<BabyBearField>,
}

impl Avx512SameSizeChain {
    pub fn new(
        prog: crate::gkr::prover::sumcheck_loop::OwnedSoaProgram<BabyBearField, BabyBearExt4>,
    ) -> Self {
        let omega16_bb = ::fft::domain_generator_for_size::<BabyBearField>(16);
        for form in prog.forms.iter() {
            for (_, idx) in form.members.iter() {
                assert!(prog.base_interp[*idx as usize]);
            }
        }
        for (a, b, _) in prog.products.iter() {
            for r in [a, b] {
                if let crate::gkr::prover::sumcheck_loop::windowed_mode::program::FormRef::Slot(i) =
                    r
                {
                    assert!(prog.base_interp[*i as usize]);
                }
            }
        }
        let folded_interp: Vec<bool> = prog
            .base_interp
            .iter()
            .chain(prog.ext_interp.iter())
            .copied()
            .collect();
        // the per-row L1 footprint of the initial pass: every base slot and
        // form grid is 128 B, every ext grid 512 B (two rows per block)
        let (nb, ne, nf) = (prog.base_interp.len(), prog.ext_interp.len(), prog.forms.len());
        use crate::gkr::prover::sumcheck_loop::windowed_mode::program::ProgramStep;
        let count = |f: &dyn Fn(&ProgramStep<BabyBearExt4>) -> bool| prog.rest_steps.iter().filter(|s| f(s)).count();
        println!(
            "[ss-program] {nb} base slots ({} interpolated), {ne} ext slots, {nf} forms, {} factored products, {} rest steps (QuadBB {}, LinB {}, QuadBE {}, QuadEE {}, LinE {}); per-row grids {:.1} KB (x2 rows), continuing {:.1} KB",
            prog.base_interp.iter().filter(|b| **b).count(),
            prog.products.len(),
            prog.rest_steps.len(),
            count(&|s| matches!(s, ProgramStep::QuadBB { .. })),
            count(&|s| matches!(s, ProgramStep::LinB { .. })),
            count(&|s| matches!(s, ProgramStep::QuadBE { .. })),
            count(&|s| matches!(s, ProgramStep::QuadEE { .. })),
            count(&|s| matches!(s, ProgramStep::LinE { .. })),
            ((nb + nf) * 128 + ne * 512) as f64 / 1024.0,
            ((nb + ne + nf) * 512) as f64 / 1024.0,
        );
        Self {
            prog,
            folded_interp,
            mat: lsb_generic::Lde8Matrix::new(omega16_bb),
        }
    }
}

impl crate::gkr::prover::sumcheck_loop::SameSizeChainOps<BabyBearField, BabyBearExt4>
    for Avx512SameSizeChain
{
    fn uniskip_initial_pass(
        &self,
        base_polys: &[&[BabyBearField]],
        ext_polys: &[&[BabyBearExt4]],
        eq_suffix: &[BabyBearExt4],
        out_size: usize,
        worker: &Worker,
    ) -> [BabyBearExt4; 16] {
        use crate::gkr::prover::sumcheck_loop::windowed_mode::lsb_chain::quasi;
        lsb_generic::head_pass::<BabyBearField, BabyBearExt4>(
            &quasi::<BabyBearField, false>(base_polys),
            &quasi::<BabyBearExt4, false>(ext_polys),
            &self.prog,
            &self.mat,
            eq_suffix,
            out_size,
            worker,
        )
    }

    fn uniskip_continuing_pass(
        &self,
        folded: &[&[BabyBearExt4]],
        eq_suffix: &[BabyBearExt4],
        out_size: usize,
        worker: &Worker,
    ) -> [BabyBearExt4; 16] {
        use crate::gkr::prover::sumcheck_loop::windowed_mode::lsb_chain::quasi;
        lsb_generic::ext_pass::<BabyBearField, BabyBearExt4>(
            &quasi::<BabyBearExt4, false>(folded),
            &self.prog,
            &self.mat,
            eq_suffix,
            out_size,
            worker,
        )
    }

    fn window_initial_pass(
        &self,
        base_polys: &[&[BabyBearField]],
        ext_polys: &[&[BabyBearExt4]],
        eq_suffix: &[BabyBearExt4],
        out_size: usize,
        worker: &Worker,
    ) -> [BabyBearExt4; 27] {
        use crate::gkr::prover::sumcheck_loop::windowed_mode::lsb_chain::quasi;
        let base_srcs = quasi::<BabyBearField, false>(base_polys);
        let ext_srcs = quasi::<BabyBearExt4, false>(ext_polys);
        let acc = if out_size % 2 == 0 {
            lsb_avx512::lsb_soa_full_parallel_w3(
                &base_srcs,
                &ext_srcs,
                &self.prog.base_interp,
                &self.prog.ext_interp,
                &self.prog.forms,
                &self.prog.products,
                &self.prog.rest_steps,
                &self.prog.additive_constant,
                eq_suffix,
                out_size,
                worker,
            )
        } else {
            lsb_avx2::lsb_soa_full_parallel_w3::<1>(
                &base_srcs,
                &ext_srcs,
                &self.prog.base_interp,
                &self.prog.ext_interp,
                &self.prog.forms,
                &self.prog.products,
                &self.prog.rest_steps,
                &self.prog.additive_constant,
                eq_suffix,
                out_size,
                worker,
            )
        };
        core::array::from_fn(|g| acc[lsb_avx2::w3_soa_cell_of_generic(g)])
    }

    fn window_continuing_pass(
        &self,
        folded: &[&[BabyBearExt4]],
        eq_suffix: &[BabyBearExt4],
        out_size: usize,
        worker: &Worker,
    ) -> [BabyBearExt4; 27] {
        use crate::gkr::prover::sumcheck_loop::windowed_mode::lsb_chain::quasi;
        let srcs = quasi::<BabyBearExt4, false>(folded);
        let acc = lsb_avx512::lsb_soa_ext_pass_parallel_w3(
            &srcs,
            &self.folded_interp,
            &self.prog.forms,
            &self.prog.products,
            &self.prog.folded_quad,
            &self.prog.folded_lin,
            &self.prog.additive_constant,
            eq_suffix,
            out_size,
            worker,
        );
        core::array::from_fn(|g| acc[lsb_avx2::w3_soa_cell_of_generic(g)])
    }

    fn fold_initial(
        &self,
        base_polys: &[&[BabyBearField]],
        ext_polys: &[&[BabyBearExt4]],
        weights: &[BabyBearExt4; 8],
        trackers: &mut [FoldBufferTracker<BabyBearExt4>],
        worker: &Worker,
    ) {
        use crate::gkr::prover::sumcheck_loop::windowed_mode::lsb_chain::chain_fold_dst;
        use crate::gkr::sumcheck::access_and_fold::DisjointAccessQuasiSlice;
        let nb = base_polys.len();
        assert_eq!(trackers.len(), nb + ext_polys.len());
        for (i, src) in base_polys.iter().enumerate() {
            let rows = src.len() / 8;
            let dst = chain_fold_dst(&trackers[i], rows);
            if rows % 16 == 0 {
                lsb_avx512::lsb_fold_base_parallel(src.as_ptr() as *const u8, dst, weights, worker);
            } else if rows % 8 == 0 {
                lsb_avx2::lsb_fold_base_soa_parallel(
                    src.as_ptr() as *const u8,
                    dst,
                    weights,
                    worker,
                );
            } else {
                let q = DisjointAccessQuasiSlice::<_, false>::from_init_slice(src);
                lsb_generic::fold_base::<BabyBearField, BabyBearExt4>(&q, dst, weights, worker);
            }
        }
        for (i, src) in ext_polys.iter().enumerate() {
            let rows = src.len() / 8;
            let dst = chain_fold_dst(&trackers[nb + i], rows);
            if rows % 16 == 0 {
                lsb_avx512::lsb_fold_ext_parallel(src.as_ptr() as *const u8, dst, weights, worker);
            } else if rows % 8 == 0 {
                lsb_avx2::lsb_fold_ext_soa_parallel(
                    src.as_ptr() as *const u8,
                    dst,
                    weights,
                    worker,
                );
            } else {
                lsb_generic::fold_ext::<BabyBearExt4>(
                    crate::gkr::prover::SendConstPtr(src.as_ptr()),
                    dst,
                    weights,
                    worker,
                );
            }
        }
    }

    fn fold_continuing(
        &self,
        weights: &[BabyBearExt4; 8],
        trackers: &mut [FoldBufferTracker<BabyBearExt4>],
        worker: &Worker,
    ) {
        use crate::gkr::prover::sumcheck_loop::windowed_mode::lsb_chain::chain_fold_dst;
        for tracker in trackers.iter_mut() {
            let fold_out = tracker.output_len();
            assert_eq!(tracker.input_len(), 8 * fold_out);
            let src_ptr = tracker.input_ptr_range().start;
            let dst = chain_fold_dst(tracker, fold_out);
            if fold_out % 16 == 0 {
                lsb_avx512::lsb_fold_ext_parallel(src_ptr as *const u8, dst, weights, worker);
            } else if fold_out % 8 == 0 {
                lsb_avx2::lsb_fold_ext_soa_parallel(src_ptr as *const u8, dst, weights, worker);
            } else {
                lsb_generic::fold_ext::<BabyBearExt4>(
                    crate::gkr::prover::SendConstPtr(src_ptr),
                    dst,
                    weights,
                    worker,
                );
            }
        }
    }

    fn tail_round_message(
        &self,
        trackers: &[FoldBufferTracker<BabyBearExt4>],
        tail_t_table: &[BabyBearExt4],
        worker: &Worker,
    ) -> (BabyBearExt4, BabyBearExt4) {
        crate::gkr::prover::sumcheck_loop::windowed_mode::lsb_chain::tail_round_message_with_program(
            &self.prog,
            trackers,
            tail_t_table,
            worker,
        )
    }
}

/// The same-size chain executor of [`X86GKRBackend`]: the AVX-512 or the
/// AVX2 executor, chosen at backend construction.
pub enum X86SameSizeChain {
    Avx2(super::avx2::Avx2SameSizeChain),
    Avx512(Avx512SameSizeChain),
}

macro_rules! x86_chain_delegate {
    ($self:ident, $method:ident ( $($arg:expr),* )) => {
        match $self {
            X86SameSizeChain::Avx2(c) => c.$method($($arg),*),
            X86SameSizeChain::Avx512(c) => c.$method($($arg),*),
        }
    };
}

impl crate::gkr::prover::sumcheck_loop::SameSizeChainOps<BabyBearField, BabyBearExt4>
    for X86SameSizeChain
{
    fn uniskip_initial_pass(
        &self,
        base_polys: &[&[BabyBearField]],
        ext_polys: &[&[BabyBearExt4]],
        eq_suffix: &[BabyBearExt4],
        out_size: usize,
        worker: &Worker,
    ) -> [BabyBearExt4; 16] {
        x86_chain_delegate!(self, uniskip_initial_pass(base_polys, ext_polys, eq_suffix, out_size, worker))
    }
    fn uniskip_continuing_pass(
        &self,
        folded: &[&[BabyBearExt4]],
        eq_suffix: &[BabyBearExt4],
        out_size: usize,
        worker: &Worker,
    ) -> [BabyBearExt4; 16] {
        x86_chain_delegate!(self, uniskip_continuing_pass(folded, eq_suffix, out_size, worker))
    }
    fn window_initial_pass(
        &self,
        base_polys: &[&[BabyBearField]],
        ext_polys: &[&[BabyBearExt4]],
        eq_suffix: &[BabyBearExt4],
        out_size: usize,
        worker: &Worker,
    ) -> [BabyBearExt4; 27] {
        x86_chain_delegate!(self, window_initial_pass(base_polys, ext_polys, eq_suffix, out_size, worker))
    }
    fn window_continuing_pass(
        &self,
        folded: &[&[BabyBearExt4]],
        eq_suffix: &[BabyBearExt4],
        out_size: usize,
        worker: &Worker,
    ) -> [BabyBearExt4; 27] {
        x86_chain_delegate!(self, window_continuing_pass(folded, eq_suffix, out_size, worker))
    }
    fn fold_initial(
        &self,
        base_polys: &[&[BabyBearField]],
        ext_polys: &[&[BabyBearExt4]],
        weights: &[BabyBearExt4; 8],
        trackers: &mut [FoldBufferTracker<BabyBearExt4>],
        worker: &Worker,
    ) {
        x86_chain_delegate!(self, fold_initial(base_polys, ext_polys, weights, trackers, worker))
    }
    fn fold_continuing(
        &self,
        weights: &[BabyBearExt4; 8],
        trackers: &mut [FoldBufferTracker<BabyBearExt4>],
        worker: &Worker,
    ) {
        x86_chain_delegate!(self, fold_continuing(weights, trackers, worker))
    }
    fn tail_round_message(
        &self,
        trackers: &[FoldBufferTracker<BabyBearExt4>],
        tail_t_table: &[BabyBearExt4],
        worker: &Worker,
    ) -> (BabyBearExt4, BabyBearExt4) {
        x86_chain_delegate!(self, tail_round_message(trackers, tail_t_table, worker))
    }
}

/// The x86-64 BabyBear/Ext4 backend: AVX-512 same-size kernels when
/// `avx512f` is present (AVX2 otherwise), AVX2 dimension-reducing kernels,
/// and the fold buffer pool.
pub struct X86GKRBackend {
    use_avx512: bool,
    pool: FoldBufferPool,
    /// cross-proof pool of the storage's extension polys (enabled with `pooled`)
    ext_pool: Option<std::sync::Arc<crate::gkr::sumcheck::access_and_fold::ExtPolyPool<BabyBearExt4>>>,
}

impl X86GKRBackend {
    /// Explicit selection: `use_avx512` requires `avx512f` (panics
    /// otherwise); `pooled` enables the pre-touched fold buffer pool.
    pub fn new(use_avx512: bool, pooled: bool) -> Self {
        assert!(
            !use_avx512 || is_x86_feature_detected!("avx512f"),
            "X86GKRBackend: avx512f requested but not available"
        );
        Self {
            use_avx512,
            pool: FoldBufferPool::new(pooled),
            ext_pool: pooled.then(|| {
                std::sync::Arc::new(crate::gkr::sumcheck::access_and_fold::ExtPolyPool::new())
            }),
        }
    }
    /// Runtime-detected kernels (AVX-512 when `avx512f` is present) with the pool.
    pub fn detect() -> Self {
        Self::new(is_x86_feature_detected!("avx512f"), true)
    }
    pub fn uses_avx512(&self) -> bool {
        self.use_avx512
    }
}

impl Default for X86GKRBackend {
    fn default() -> Self {
        Self::detect()
    }
}

impl GKRBackend<BabyBearField, BabyBearExt4> for X86GKRBackend {
    type DimensionReducingBuffer = DimReducingSumcheckScratch<BabyBearExt4, [u128; 2]>;

    fn ext_poly_pool(
        &self,
    ) -> Option<std::sync::Arc<crate::gkr::sumcheck::access_and_fold::ExtPolyPool<BabyBearExt4>>>
    {
        self.ext_pool.clone()
    }

    fn prepare_fold_pool(&self, shapes: &[(usize, usize)], worker: &Worker) {
        // the same-size shape's count must cover the DR count too when its
        // buffers are the smaller ones: hand the DR path the LARGER size and
        // keep the remaining same-size buffers at their own size
        let (dr, ss) = (shapes[0], shapes[1]);
        let big = dr.1.max(ss.1);
        let merged = [(dr.0, big), (ss.0.saturating_sub(dr.0), ss.1)];
        self.pool.prefill(&merged, worker);
    }

    fn make_dim_reducing_work_buffers(
        &self,
        max_rounds: usize,
        max_polys: usize,
        worker: &Worker,
    ) -> Self::DimensionReducingBuffer {
        let m = 1usize << max_rounds;
        let mut scratch = DimReducingSumcheckScratch::new(0, 0, worker);
        scratch.fold = self.pool.take(max_polys, m + m / 2);
        let tri_cap = (m / 2)
            .div_ceil(worker.num_cores)
            .max(crate::gkr::PAR_THRESHOLD);
        scratch.tri = (0..worker.num_cores)
            .map(|_| Box::new_uninit_slice(tri_cap))
            .collect();
        scratch
    }

    fn recycle_dim_reducing_work_buffers(&self, buffers: Self::DimensionReducingBuffer) {
        self.pool.give(buffers.fold);
    }

    fn dimension_reduction_forward(
        &self,
        storage: &mut GKRStorage<BabyBearField, BabyBearExt4>,
        compiled_circuit: &GKRCircuitArtifact<BabyBearField>,
        initial_trace_log_2: usize,
        final_trace_log_2: usize,
        worker: &Worker,
    ) -> (
        usize,
        BTreeMap<usize, BTreeMap<OutputType, DimensionReducingInputOutput>>,
    ) {
        let use_avx512 = self.use_avx512;
        super::super::dimension_reduction::forward::evaluate_dimension_reduction_forward_with(
            storage,
            compiled_circuit,
            initial_trace_log_2,
            final_trace_log_2,
            worker,
            |s, i, o, l, n, w| super::avx512_dr::forward_pairwise_x86(s, i, o, l, n, w, use_avx512),
            |s, i, o, l, n, w| super::avx512_dr::forward_logup_x86(s, i, o, l, n, w, use_avx512),
        )
    }

    fn dimension_reducing_sumcheck_for_layer<TR: Transcript<BabyBearField, BabyBearExt4>>(
        &self,
        schedule: &[crate::gkr::prover_config::SumcheckStep],
        layer_idx: usize,
        layer: &BTreeMap<OutputType, DimensionReducingInputOutput>,
        claim_points: &mut BTreeMap<usize, Vec<EvaluationPointEntry<BabyBearExt4>>>,
        claims_storage: &mut BTreeMap<usize, BTreeMap<GKRAddress, BabyBearExt4>>,
        gkr_storage: &mut GKRStorage<BabyBearField, BabyBearExt4>,
        batching_challenge: &mut BabyBearExt4,
        seed: &mut TR::Seed,
        trace_len_after_reduction: usize,
        worker: &Worker,
        buffers: &mut Self::DimensionReducingBuffer,
    ) -> SumcheckIntermediateProofValues<BabyBearField, BabyBearExt4> {
        let use_avx512 = self.use_avx512;
        super::super::sumcheck_loop::evaluate_dimension_reducing_sumcheck_for_layer_lsb::<
            BabyBearField,
            BabyBearExt4,
            TR,
            [u128; 2],
            _,
            _,
        >(
            |cur, outs, rels, tp, cs, cl, sp| unsafe {
                if use_avx512 {
                    super::avx512_dr::avx512_initial_chunk::<BabyBearExt4>(cur, outs, rels, tp, cs, cl, sp)
                } else {
                    avx2_initial_chunk::<BabyBearExt4>(cur, outs, rels, tp, cs, cl, sp)
                }
            },
            |buffers, rels, r, tp, cs, cl, sp| unsafe {
                if use_avx512 {
                    super::avx512_dr::avx512_continuing_chunk::<BabyBearExt4>(buffers, rels, r, tp, cs, cl, sp)
                } else {
                    avx2_continuing_chunk::<BabyBearExt4>(buffers, rels, r, tp, cs, cl, sp)
                }
            },
            schedule,
            layer_idx,
            layer,
            claim_points,
            claims_storage,
            gkr_storage,
            batching_challenge,
            seed,
            trace_len_after_reduction,
            worker,
            buffers,
        )
    }

    type NaiveSameSizeFoldBuffer = FoldBuf;
    type WindowedSameSizeFoldBuffer = FoldBuf;
    type UniskipSameSizeFoldBuffer = FoldBuf;

    fn make_naive_same_size_fold_buffers(
        &self,
        _schedule: &[crate::gkr::prover_config::SumcheckStep],
        _trace_len: usize,
        _num_base_polys: usize,
        _num_ext_polys: usize,
    ) -> Vec<Self::NaiveSameSizeFoldBuffer> {
        Vec::new()
    }

    fn make_windowed_same_size_fold_buffers(
        &self,
        schedule: &[crate::gkr::prover_config::SumcheckStep],
        trace_len: usize,
        num_base_polys: usize,
        num_ext_polys: usize,
    ) -> Vec<Self::WindowedSameSizeFoldBuffer> {
        let capacity = super::same_size_chain_fold_capacity(schedule, trace_len);
        self.pool.take(num_base_polys + num_ext_polys, capacity)
    }

    fn make_uniskip_same_size_fold_buffers(
        &self,
        schedule: &[crate::gkr::prover_config::SumcheckStep],
        trace_len: usize,
        num_base_polys: usize,
        num_ext_polys: usize,
    ) -> Vec<Self::UniskipSameSizeFoldBuffer> {
        let capacity = super::same_size_chain_fold_capacity(schedule, trace_len);
        self.pool.take(num_base_polys + num_ext_polys, capacity)
    }

    fn recycle_same_size_fold_buffers(&self, buffers: Vec<FoldBuf>) {
        self.pool.give(buffers);
    }

    type SameSizeChain = X86SameSizeChain;

    fn make_same_size_chain(
        &self,
        prog: crate::gkr::prover::sumcheck_loop::OwnedSoaProgram<BabyBearField, BabyBearExt4>,
    ) -> Self::SameSizeChain {
        if self.use_avx512 {
            X86SameSizeChain::Avx512(Avx512SameSizeChain::new(prog))
        } else {
            X86SameSizeChain::Avx2(super::avx2::Avx2SameSizeChain::new(prog))
        }
    }

    fn evaluate_same_size_sumcheck_for_layer<TR: Transcript<BabyBearField, BabyBearExt4>>(
        &self,
        layer_idx: usize,
        layer: &cs::gkr_compiler::GKRLayerDescription<BabyBearField>,
        claim_points: &mut BTreeMap<usize, Vec<EvaluationPointEntry<BabyBearExt4>>>,
        claims_storage: &mut BTreeMap<usize, BTreeMap<GKRAddress, BabyBearExt4>>,
        gkr_storage: &mut GKRStorage<BabyBearField, BabyBearExt4>,
        batching_challenge: &mut BabyBearExt4,
        trace_len: usize,
        lookup_challenges_multiplicative_part: BabyBearExt4,
        lookup_challenges_additive_part: BabyBearExt4,
        inits_and_teardowns_top_bits: &[u32],
        address_high_bits_shift: u32,
        external_challenges: &super::super::GKRExternalChallenges<BabyBearField, BabyBearExt4>,
        prover_config: &crate::gkr::prover_config::ProverConfig,
        seed: &mut TR::Seed,
        worker: &Worker,
    ) -> SumcheckIntermediateProofValues<BabyBearField, BabyBearExt4> {
        super::super::sumcheck_loop::evaluate_sumcheck_for_layer::<BabyBearField, BabyBearExt4, TR, _>(
            layer_idx,
            layer,
            claim_points,
            claims_storage,
            gkr_storage,
            batching_challenge,
            trace_len,
            lookup_challenges_multiplicative_part,
            lookup_challenges_additive_part,
            inits_and_teardowns_top_bits,
            address_high_bits_shift,
            external_challenges,
            prover_config,
            seed,
            worker,
            |s, t, b, e| self.make_uniskip_same_size_fold_buffers(s, t, b, e),
            |s, t, b, e| self.make_windowed_same_size_fold_buffers(s, t, b, e),
            |prog| self.make_same_size_chain(prog),
            |bufs| self.recycle_same_size_fold_buffers(bufs),
        )
    }
}
