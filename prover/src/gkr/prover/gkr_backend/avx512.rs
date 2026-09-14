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

use crate::allocation_pool::AllocationPool;
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
use field::{Field, FieldExtension};
use transcript::Transcript;
use worker::Worker;

pub type FoldBuf = Box<[core::mem::MaybeUninit<BabyBearExt4>]>;

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
        let (nb, ne, nf) = (
            prog.base_interp.len(),
            prog.ext_interp.len(),
            prog.forms.len(),
        );
        use crate::gkr::prover::sumcheck_loop::windowed_mode::program::ProgramStep;
        let count = |f: &dyn Fn(&ProgramStep<BabyBearExt4>) -> bool| {
            prog.rest_steps.iter().filter(|s| f(s)).count()
        };
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
        x86_chain_delegate!(
            self,
            uniskip_initial_pass(base_polys, ext_polys, eq_suffix, out_size, worker)
        )
    }
    fn uniskip_continuing_pass(
        &self,
        folded: &[&[BabyBearExt4]],
        eq_suffix: &[BabyBearExt4],
        out_size: usize,
        worker: &Worker,
    ) -> [BabyBearExt4; 16] {
        x86_chain_delegate!(
            self,
            uniskip_continuing_pass(folded, eq_suffix, out_size, worker)
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
        x86_chain_delegate!(
            self,
            window_initial_pass(base_polys, ext_polys, eq_suffix, out_size, worker)
        )
    }
    fn window_continuing_pass(
        &self,
        folded: &[&[BabyBearExt4]],
        eq_suffix: &[BabyBearExt4],
        out_size: usize,
        worker: &Worker,
    ) -> [BabyBearExt4; 27] {
        x86_chain_delegate!(
            self,
            window_continuing_pass(folded, eq_suffix, out_size, worker)
        )
    }
    fn fold_initial(
        &self,
        base_polys: &[&[BabyBearField]],
        ext_polys: &[&[BabyBearExt4]],
        weights: &[BabyBearExt4; 8],
        trackers: &mut [FoldBufferTracker<BabyBearExt4>],
        worker: &Worker,
    ) {
        x86_chain_delegate!(
            self,
            fold_initial(base_polys, ext_polys, weights, trackers, worker)
        )
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
}

impl X86GKRBackend {
    /// Explicit selection: `use_avx512` requires `avx512f` (panics
    /// otherwise). Buffer pooling is the [`AllocationPool`]'s business.
    pub fn new(use_avx512: bool) -> Self {
        assert!(
            !use_avx512 || is_x86_feature_detected!("avx512f"),
            "X86GKRBackend: avx512f requested but not available"
        );
        Self { use_avx512 }
    }
    /// Runtime-detected kernels (AVX-512 when `avx512f` is present).
    pub fn detect() -> Self {
        Self::new(is_x86_feature_detected!("avx512f"))
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
    fn fold_eq_poly_into(
        &self,
        src: &[BabyBearExt4],
        challenge: &BabyBearExt4,
        dst: &mut [core::mem::MaybeUninit<BabyBearExt4>],
        worker: &Worker,
    ) {
        if self.use_avx512 {
            fold_eq_poly_into_avx512(src, challenge, dst, worker);
        } else {
            super::fold_eq_poly_into_scalar::<BabyBearField, BabyBearExt4>(
                src, challenge, dst, worker,
            );
        }
    }

    fn accumulate_base_columns_into(
        &self,
        dst: &mut [core::mem::MaybeUninit<BabyBearExt4>],
        terms: &[super::BatchedBaseColumn<'_, BabyBearField, BabyBearExt4>],
        worker: &Worker,
    ) {
        if self.use_avx512 {
            accumulate_base_columns_into_avx512(dst, terms, worker);
        } else {
            super::accumulate_base_columns_into_scalar::<BabyBearField, BabyBearExt4>(
                dst, terms, worker,
            );
        }
    }

    type DimensionReducingBuffer = DimReducingSumcheckScratch<BabyBearExt4, [u128; 2]>;

    fn prepare_fold_pool(
        &self,
        shapes: &[(usize, usize)],
        pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
        worker: &Worker,
    ) {
        // pre-touch the fold scratch of both passes: the dimension-reducing
        // scratch and the same-size chain buffers are exact-length boxes
        let t = std::time::Instant::now();
        let before = pool.stats();
        for &(count, cap) in shapes.iter() {
            if count > 0 && cap > 0 {
                pool.prefill_boxes::<BabyBearExt4>(cap, count, worker);
            }
        }
        let after = pool.stats();
        println!(
            "[pool] fold buffers: shapes {:?}, {:.1} MB fresh, in {:?}",
            shapes,
            (after.retained_bytes as f64 - before.retained_bytes as f64) / 1e6,
            t.elapsed()
        );
    }

    fn make_dim_reducing_work_buffers(
        &self,
        max_rounds: usize,
        max_polys: usize,
        pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
        worker: &Worker,
    ) -> Self::DimensionReducingBuffer {
        DimReducingSumcheckScratch::new(max_rounds, max_polys, pool, worker)
    }

    fn recycle_dim_reducing_work_buffers(
        &self,
        buffers: Self::DimensionReducingBuffer,
        pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
    ) {
        buffers.release(pool);
    }

    fn dimension_reduction_forward(
        &self,
        storage: &mut GKRStorage<BabyBearField, BabyBearExt4>,
        compiled_circuit: &GKRCircuitArtifact<BabyBearField>,
        initial_trace_log_2: usize,
        final_trace_log_2: usize,
        pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
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
            pool,
            worker,
            |s, i, o, l, n, p, w| {
                super::avx512_dr::forward_pairwise_x86(s, i, o, l, n, p, w, use_avx512)
            },
            |s, i, o, l, n, p, w| {
                super::avx512_dr::forward_logup_x86(s, i, o, l, n, p, w, use_avx512)
            },
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
        pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
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
                    super::avx512_dr::avx512_initial_chunk::<BabyBearExt4>(
                        cur, outs, rels, tp, cs, cl, sp,
                    )
                } else {
                    avx2_initial_chunk::<BabyBearExt4>(cur, outs, rels, tp, cs, cl, sp)
                }
            },
            |buffers, rels, r, tp, cs, cl, sp| unsafe {
                if use_avx512 {
                    super::avx512_dr::avx512_continuing_chunk::<BabyBearExt4>(
                        buffers, rels, r, tp, cs, cl, sp,
                    )
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
            pool,
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
        _pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
    ) -> Vec<Self::NaiveSameSizeFoldBuffer> {
        Vec::new()
    }

    fn make_windowed_same_size_fold_buffers(
        &self,
        schedule: &[crate::gkr::prover_config::SumcheckStep],
        trace_len: usize,
        num_base_polys: usize,
        num_ext_polys: usize,
        pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
    ) -> Vec<Self::WindowedSameSizeFoldBuffer> {
        let capacity = super::same_size_chain_fold_capacity(schedule, trace_len);
        (0..num_base_polys + num_ext_polys)
            .map(|_| pool.alloc_box(capacity))
            .collect()
    }

    fn make_uniskip_same_size_fold_buffers(
        &self,
        schedule: &[crate::gkr::prover_config::SumcheckStep],
        trace_len: usize,
        num_base_polys: usize,
        num_ext_polys: usize,
        pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
    ) -> Vec<Self::UniskipSameSizeFoldBuffer> {
        let capacity = super::same_size_chain_fold_capacity(schedule, trace_len);
        (0..num_base_polys + num_ext_polys)
            .map(|_| pool.alloc_box(capacity))
            .collect()
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
        pool: &dyn AllocationPool<BabyBearField, BabyBearExt4>,
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
            pool,
            worker,
            |s, t, b, e| self.make_uniskip_same_size_fold_buffers(s, t, b, e, pool),
            |s, t, b, e| self.make_windowed_same_size_fold_buffers(s, t, b, e, pool),
            |prog| self.make_same_size_chain(prog),
            |bufs| self.recycle_same_size_fold_buffers(bufs, pool),
        )
    }
}

/// Worker-parallel [`GKRBackend::fold_eq_poly_into`] on the AVX-512 pair
/// kernel: the pairs are split into chunks that are multiples of 16 (so only
/// the last chunk can have a scalar tail).
fn fold_eq_poly_into_avx512(
    src: &[BabyBearExt4],
    challenge: &BabyBearExt4,
    dst: &mut [core::mem::MaybeUninit<BabyBearExt4>],
    worker: &Worker,
) {
    use worker::rayon::prelude::*;
    assert!(src.len().is_power_of_two());
    let half = src.len() / 2;
    assert!(dst.len() >= half);
    if half < 256 {
        super::fold_eq_poly_into_scalar::<BabyBearField, BabyBearExt4>(src, challenge, dst, worker);
        return;
    }
    let chunk = half
        .div_ceil(worker.get_num_cores())
        .max(crate::gkr::PAR_THRESHOLD)
        .next_multiple_of(16);
    let n_chunks = half.div_ceil(chunk);
    let src_addr = src.as_ptr() as usize;
    let dst_addr = dst.as_mut_ptr() as usize;
    worker.pool.install(|| {
        (0..n_chunks).into_par_iter().for_each(|c| {
            let lo = c * chunk;
            let hi = (lo + chunk).min(half);
            unsafe {
                crate::gkr::prover::sumcheck_loop::windowed_mode::avx512::fold_pairs_avx512(
                    (src_addr as *const BabyBearExt4).add(2 * lo),
                    hi - lo,
                    challenge,
                    (dst_addr as *mut BabyBearExt4).add(lo),
                );
            }
        });
    });
}

/// AVX-512 [`GKRBackend::accumulate_base_columns_into`]: per 16 rows the
/// accumulator lives in limb-major registers; every column contributes one
/// 16-lane load and four `mont_mul + add` (its base value times each limb
/// of the column's weight), then the 16 ext values are streamed out
/// (non-temporal — the destination is read next by the whole-poly
/// transform, far beyond any cache). Byte-identical to the scalar loop.
fn accumulate_base_columns_into_avx512(
    dst: &mut [core::mem::MaybeUninit<BabyBearExt4>],
    terms: &[super::BatchedBaseColumn<'_, BabyBearField, BabyBearExt4>],
    worker: &Worker,
) {
    use worker::rayon::prelude::*;
    let n = terms.first().map(|t| t.column.len()).unwrap_or(dst.len());
    assert!(n > 0 && dst.len() % n == 0);
    for t in terms.iter() {
        assert_eq!(t.column.len(), n);
        assert!(t.dst_offset % n == 0 && t.dst_offset + n <= dst.len());
    }
    let slices = dst.len() / n;
    let chunk = n
        .div_ceil(worker.get_num_cores())
        .max(crate::gkr::PAR_THRESHOLD)
        .next_multiple_of(16);
    let n_chunks = n.div_ceil(chunk);
    for y in 0..slices {
        let off = y * n;
        let slice_terms: Vec<(usize, BabyBearExt4)> = terms
            .iter()
            .filter(|t| t.dst_offset == off)
            .map(|t| (t.column.as_ptr() as usize, t.power))
            .collect();
        let dst_addr = dst[off..].as_mut_ptr() as usize;
        let slice_terms = &slice_terms;
        worker.pool.install(|| {
            (0..n_chunks).into_par_iter().for_each(|c| {
                let lo = c * chunk;
                let hi = (lo + chunk).min(n);
                unsafe {
                    accumulate_rows_avx512(
                        (dst_addr as *mut BabyBearExt4).add(lo),
                        hi - lo,
                        lo,
                        slice_terms,
                    );
                }
            });
        });
    }
}

/// `rows` rows from `row0` of every term into `dst` (see
/// [`accumulate_base_columns_into_avx512`]).
#[target_feature(enable = "avx512f")]
unsafe fn accumulate_rows_avx512(
    dst: *mut BabyBearExt4,
    rows: usize,
    row0: usize,
    terms: &[(usize, BabyBearExt4)],
) {
    use crate::gkr::prover::sumcheck_loop::windowed_mode::avx512::{
        add16, bcast_ext, ld, mont_mul16, store_ext16_nt, zero, ExtPerm,
    };
    use core::arch::x86_64::*;
    let p = ExtPerm::new();
    let weights: Vec<[__m512i; 4]> = terms.iter().map(|(_, w)| bcast_ext(w)).collect();
    let full = rows / 16;
    for blk in 0..full {
        let mut acc = [zero(); 4];
        for ((col, _), w) in terms.iter().zip(weights.iter()) {
            let b = ld((*col as *const u32).add(row0 + blk * 16));
            for l in 0..4 {
                acc[l] = add16(acc[l], mont_mul16(b, w[l]));
            }
        }
        store_ext16_nt(&acc, dst.add(blk * 16), &p);
    }
    for i in full * 16..rows {
        let mut v = BabyBearExt4::ZERO;
        for (col, w) in terms.iter() {
            let s = *(*col as *const BabyBearField).add(row0 + i);
            v.add_assign_product_with_base(w, &s);
        }
        dst.add(i).write(v);
    }
    _mm_sfence();
}

#[cfg(test)]
mod accumulate_tests {
    use super::*;
    use field::Rand;

    #[test]
    fn avx512_accumulate_base_columns_matches_scalar() {
        if !is_x86_feature_detected!("avx512f") {
            eprintln!("avx512f not available: skipping");
            return;
        }
        let worker = Worker::new_with_num_threads(4);
        let mut rng = rand::thread_rng();
        for (n, slices, num_cols) in [
            (1usize << 10, 1usize, 5usize),
            ((1 << 12) + 48, 2, 7),
            (37, 1, 3),
            (1 << 13, 1, 0),
        ] {
            let cols: Vec<Vec<BabyBearField>> = (0..num_cols)
                .map(|_| {
                    (0..n)
                        .map(|_| BabyBearField::random_element(&mut rng))
                        .collect()
                })
                .collect();
            let terms: Vec<super::super::BatchedBaseColumn<'_, BabyBearField, BabyBearExt4>> = cols
                .iter()
                .enumerate()
                .map(|(j, c)| super::super::BatchedBaseColumn {
                    column: &c[..],
                    power: BabyBearExt4::random_element(&mut rng),
                    dst_offset: (j % slices) * n,
                })
                .collect();
            let len = n * slices;
            let mut a: Vec<core::mem::MaybeUninit<BabyBearExt4>> = Vec::with_capacity(len);
            let mut b: Vec<core::mem::MaybeUninit<BabyBearExt4>> = Vec::with_capacity(len);
            unsafe {
                a.set_len(len);
                b.set_len(len);
            }
            super::super::accumulate_base_columns_into_scalar::<BabyBearField, BabyBearExt4>(
                &mut a, &terms, &worker,
            );
            accumulate_base_columns_into_avx512(&mut b, &terms, &worker);
            let a: Vec<BabyBearExt4> = a.iter().map(|x| unsafe { x.assume_init() }).collect();
            let b: Vec<BabyBearExt4> = b.iter().map(|x| unsafe { x.assume_init() }).collect();
            assert_eq!(a, b, "n {n} slices {slices} cols {num_cols}");
            // the scalar reference itself against the definition
            for y in 0..slices {
                for i in 0..n {
                    let mut v = BabyBearExt4::ZERO;
                    for t in terms.iter().filter(|t| t.dst_offset == y * n) {
                        let mut w = t.power;
                        w.mul_assign_by_base(&t.column[i]);
                        v.add_assign(&w);
                    }
                    assert_eq!(a[y * n + i], v);
                }
            }
        }
    }
}

#[cfg(test)]
mod fold_eq_tests {
    use super::*;
    use field::Rand;

    #[test]
    fn avx512_fold_eq_poly_matches_scalar() {
        if !is_x86_feature_detected!("avx512f") {
            eprintln!("avx512f not available: skipping");
            return;
        }
        let worker = Worker::new_with_num_threads(4);
        let mut rng = rand::thread_rng();
        for log_n in [6usize, 12, 16] {
            let n = 1usize << log_n;
            let src: Vec<BabyBearExt4> = (0..n)
                .map(|_| BabyBearExt4::random_element(&mut rng))
                .collect();
            let ch = BabyBearExt4::random_element(&mut rng);
            let mut a: Vec<core::mem::MaybeUninit<BabyBearExt4>> = Vec::with_capacity(n / 2);
            let mut b: Vec<core::mem::MaybeUninit<BabyBearExt4>> = Vec::with_capacity(n / 2);
            unsafe {
                a.set_len(n / 2);
                b.set_len(n / 2);
            }
            super::super::fold_eq_poly_into_scalar::<BabyBearField, BabyBearExt4>(
                &src, &ch, &mut a, &worker,
            );
            fold_eq_poly_into_avx512(&src, &ch, &mut b, &worker);
            let a: Vec<BabyBearExt4> = a.iter().map(|x| unsafe { x.assume_init() }).collect();
            let b: Vec<BabyBearExt4> = b.iter().map(|x| unsafe { x.assume_init() }).collect();
            assert_eq!(a, b, "log_n {log_n}");
        }
        // the raw kernel's scalar tail
        let n_pairs = 37usize;
        let src: Vec<BabyBearExt4> = (0..2 * n_pairs)
            .map(|_| BabyBearExt4::random_element(&mut rng))
            .collect();
        let ch = BabyBearExt4::random_element(&mut rng);
        let mut out = vec![BabyBearExt4::ZERO; n_pairs];
        unsafe {
            crate::gkr::prover::sumcheck_loop::windowed_mode::avx512::fold_pairs_avx512(
                src.as_ptr(),
                n_pairs,
                &ch,
                out.as_mut_ptr(),
            );
        }
        for i in 0..n_pairs {
            let mut t = src[2 * i + 1];
            t.sub_assign(&src[2 * i]);
            t.mul_assign(&ch);
            t.add_assign(&src[2 * i]);
            assert_eq!(out[i], t, "pair {i}");
        }
    }
}
